%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YeRVR27nDL

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 100 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  348 ( 766 expanded)
%              Number of equality atoms :   13 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_tarski @ X9 @ X7 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( m1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ( r1_tarski @ ( k3_subset_1 @ X17 @ X16 ) @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
      | ( X20
        = ( k1_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('34',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YeRVR27nDL
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 233 iterations in 0.104s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(t40_subset_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.21/0.56         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56          ( ( ( r1_tarski @ B @ C ) & 
% 0.21/0.56              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.21/0.56            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.21/0.56  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d2_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X11 @ X12)
% 0.21/0.56          | (r2_hidden @ X11 @ X12)
% 0.21/0.56          | (v1_xboole_0 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.56        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf(fc1_subset_1, axiom,
% 0.21/0.56    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.56  thf('3', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.56  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf(d1_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X9 @ X8)
% 0.21/0.56          | (r1_tarski @ X9 @ X7)
% 0.21/0.56          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X7 : $i, X9 : $i]:
% 0.21/0.56         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.56  thf('7', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.56  thf('8', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t1_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.56       ( r1_tarski @ A @ C ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.56          | (r1_tarski @ X3 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.56          | (r2_hidden @ X6 @ X8)
% 0.21/0.56          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i]:
% 0.21/0.56         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.56  thf('14', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.56          | (m1_subset_1 @ X11 @ X12)
% 0.21/0.56          | (v1_xboole_0 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.56  thf(d1_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.21/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.56  thf('19', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t31_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56           ( ( r1_tarski @ B @ C ) <=>
% 0.21/0.56             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.21/0.56          | ~ (r1_tarski @ X18 @ X16)
% 0.21/0.56          | (r1_tarski @ (k3_subset_1 @ X17 @ X16) @ (k3_subset_1 @ X17 @ X18))
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.56          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.56             (k3_subset_1 @ sk_A @ X0))
% 0.21/0.56          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B_1 @ sk_C_1)
% 0.21/0.56        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.56           (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.56  thf('23', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.56        (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.56          | (r1_tarski @ X3 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ sk_B_1 @ X0)
% 0.21/0.56          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.56  thf(t38_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.56         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.21/0.56          | ((X20) = (k1_subset_1 @ X19))
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.21/0.56  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('30', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.21/0.56          | ((X20) = (k1_xboole_0))
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.56  thf('33', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.56  thf('34', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('35', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
