%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W7eujHics2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:30 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 105 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  310 ( 839 expanded)
%              Number of equality atoms :   28 (  74 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t60_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( m1_setfam_1 @ B @ A )
        <=> ( ( k5_setfam_1 @ A @ B )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_setfam_1])).

thf('0',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A )
    | ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
   <= ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( m1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) )
   <= ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k5_setfam_1 @ X10 @ X9 )
        = ( k3_tarski @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('8',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_setfam_1 @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,
    ( ~ ( m1_setfam_1 @ sk_B @ sk_A )
   <= ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
    | ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
    | ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    m1_setfam_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','17','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( ( k3_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,
    ( ( ( k3_tarski @ sk_B )
     != sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k5_setfam_1 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['5','17'])).

thf('27',plain,(
    ( k3_tarski @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ ( k3_tarski @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('33',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('35',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['28','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W7eujHics2
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.51  % Solved by: fo/fo7.sh
% 0.34/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.51  % done 45 iterations in 0.017s
% 0.34/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.51  % SZS output start Refutation
% 0.34/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.51  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.34/0.51  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.34/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.34/0.51  thf(t60_setfam_1, conjecture,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.34/0.51       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.34/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.51    (~( ![A:$i,B:$i]:
% 0.34/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.34/0.51          ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ) )),
% 0.34/0.51    inference('cnf.neg', [status(esa)], [t60_setfam_1])).
% 0.34/0.51  thf('0', plain,
% 0.34/0.51      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)) | (m1_setfam_1 @ sk_B @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('1', plain,
% 0.34/0.51      (((m1_setfam_1 @ sk_B @ sk_A)) <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.34/0.51      inference('split', [status(esa)], ['0'])).
% 0.34/0.51  thf(d12_setfam_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.34/0.51  thf('2', plain,
% 0.34/0.51      (![X6 : $i, X7 : $i]:
% 0.34/0.51         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (m1_setfam_1 @ X7 @ X6))),
% 0.34/0.51      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.34/0.51  thf('3', plain,
% 0.34/0.51      (((r1_tarski @ sk_A @ (k3_tarski @ sk_B)))
% 0.34/0.51         <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.51  thf('4', plain,
% 0.34/0.51      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)) | ~ (m1_setfam_1 @ sk_B @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('5', plain,
% 0.34/0.51      (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))) | 
% 0.34/0.51       ~ ((m1_setfam_1 @ sk_B @ sk_A))),
% 0.34/0.51      inference('split', [status(esa)], ['4'])).
% 0.34/0.51  thf('6', plain,
% 0.34/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf(redefinition_k5_setfam_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.34/0.51       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.34/0.51  thf('7', plain,
% 0.34/0.51      (![X9 : $i, X10 : $i]:
% 0.34/0.51         (((k5_setfam_1 @ X10 @ X9) = (k3_tarski @ X9))
% 0.34/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.34/0.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.34/0.51  thf('8', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.51  thf('9', plain,
% 0.34/0.51      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))
% 0.34/0.51         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.34/0.51      inference('split', [status(esa)], ['0'])).
% 0.34/0.51  thf('10', plain,
% 0.34/0.51      ((((k3_tarski @ sk_B) = (sk_A)))
% 0.34/0.51         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.34/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.34/0.51  thf(d10_xboole_0, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.51  thf('11', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.34/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.51  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.34/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.34/0.51  thf('13', plain,
% 0.34/0.51      (![X6 : $i, X8 : $i]:
% 0.34/0.51         ((m1_setfam_1 @ X8 @ X6) | ~ (r1_tarski @ X6 @ (k3_tarski @ X8)))),
% 0.34/0.51      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.34/0.51  thf('14', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.34/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.51  thf('15', plain,
% 0.34/0.51      (((m1_setfam_1 @ sk_B @ sk_A))
% 0.34/0.51         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.34/0.51      inference('sup+', [status(thm)], ['10', '14'])).
% 0.34/0.51  thf('16', plain,
% 0.34/0.51      ((~ (m1_setfam_1 @ sk_B @ sk_A)) <= (~ ((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.34/0.51      inference('split', [status(esa)], ['4'])).
% 0.34/0.51  thf('17', plain,
% 0.34/0.51      (((m1_setfam_1 @ sk_B @ sk_A)) | 
% 0.34/0.51       ~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.51  thf('18', plain,
% 0.34/0.51      (((m1_setfam_1 @ sk_B @ sk_A)) | (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.34/0.51      inference('split', [status(esa)], ['0'])).
% 0.34/0.51  thf('19', plain, (((m1_setfam_1 @ sk_B @ sk_A))),
% 0.34/0.51      inference('sat_resolution*', [status(thm)], ['5', '17', '18'])).
% 0.34/0.51  thf('20', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.34/0.51      inference('simpl_trail', [status(thm)], ['3', '19'])).
% 0.34/0.51  thf('21', plain,
% 0.34/0.51      (![X0 : $i, X2 : $i]:
% 0.34/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.51  thf('22', plain,
% 0.34/0.51      ((~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)
% 0.34/0.51        | ((k3_tarski @ sk_B) = (sk_A)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.51  thf('23', plain,
% 0.34/0.51      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)))
% 0.34/0.51         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.34/0.51      inference('split', [status(esa)], ['4'])).
% 0.34/0.51  thf('24', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.51  thf('25', plain,
% 0.34/0.51      ((((k3_tarski @ sk_B) != (sk_A)))
% 0.34/0.51         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.34/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.34/0.51  thf('26', plain, (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.34/0.51      inference('sat_resolution*', [status(thm)], ['5', '17'])).
% 0.34/0.51  thf('27', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.34/0.51      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.34/0.51  thf('28', plain, (~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.34/0.51      inference('simplify_reflect-', [status(thm)], ['22', '27'])).
% 0.34/0.51  thf('29', plain,
% 0.34/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf(t3_subset, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.51  thf('30', plain,
% 0.34/0.51      (![X11 : $i, X12 : $i]:
% 0.34/0.51         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.34/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.51  thf('31', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.51  thf(t95_zfmisc_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.34/0.51       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.34/0.51  thf('32', plain,
% 0.34/0.51      (![X3 : $i, X4 : $i]:
% 0.34/0.51         ((r1_tarski @ (k3_tarski @ X3) @ (k3_tarski @ X4))
% 0.34/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.34/0.51      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.34/0.51  thf('33', plain,
% 0.34/0.51      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.34/0.51  thf(t99_zfmisc_1, axiom,
% 0.34/0.51    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.34/0.51  thf('34', plain, (![X5 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X5)) = (X5))),
% 0.34/0.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.34/0.51  thf('35', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.34/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.34/0.51  thf('36', plain, ($false), inference('demod', [status(thm)], ['28', '35'])).
% 0.34/0.51  
% 0.34/0.51  % SZS output end Refutation
% 0.34/0.51  
% 0.34/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
