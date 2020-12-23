%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dxrPGRpwPH

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 109 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 895 expanded)
%              Number of equality atoms :   27 (  77 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( m1_setfam_1 @ X4 @ X3 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( m1_setfam_1 @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k3_tarski @ X5 ) ) ) ),
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

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('31',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('33',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['28','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dxrPGRpwPH
% 0.16/0.38  % Computer   : n022.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:46:56 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 47 iterations in 0.016s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.23/0.50  thf(t60_setfam_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50          ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t60_setfam_1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)) | (m1_setfam_1 @ sk_B @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (((m1_setfam_1 @ sk_B @ sk_A)) <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf(d12_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (m1_setfam_1 @ X4 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (((r1_tarski @ sk_A @ (k3_tarski @ sk_B)))
% 0.23/0.50         <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)) | ~ (m1_setfam_1 @ sk_B @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))) | 
% 0.23/0.50       ~ ((m1_setfam_1 @ sk_B @ sk_A))),
% 0.23/0.50      inference('split', [status(esa)], ['4'])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(redefinition_k5_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X8 : $i, X9 : $i]:
% 0.23/0.50         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.23/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.23/0.50  thf('8', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))
% 0.23/0.50         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      ((((k3_tarski @ sk_B) = (sk_A)))
% 0.23/0.50         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf(d10_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.50  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X3 : $i, X5 : $i]:
% 0.23/0.50         ((m1_setfam_1 @ X5 @ X3) | ~ (r1_tarski @ X3 @ (k3_tarski @ X5)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.23/0.50  thf('14', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (((m1_setfam_1 @ sk_B @ sk_A))
% 0.23/0.50         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.50      inference('sup+', [status(thm)], ['10', '14'])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      ((~ (m1_setfam_1 @ sk_B @ sk_A)) <= (~ ((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.23/0.50      inference('split', [status(esa)], ['4'])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (((m1_setfam_1 @ sk_B @ sk_A)) | 
% 0.23/0.50       ~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (((m1_setfam_1 @ sk_B @ sk_A)) | (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('19', plain, (((m1_setfam_1 @ sk_B @ sk_A))),
% 0.23/0.50      inference('sat_resolution*', [status(thm)], ['5', '17', '18'])).
% 0.23/0.50  thf('20', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.23/0.50      inference('simpl_trail', [status(thm)], ['3', '19'])).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      (![X0 : $i, X2 : $i]:
% 0.23/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      ((~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)
% 0.23/0.50        | ((k3_tarski @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)))
% 0.23/0.50         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.50      inference('split', [status(esa)], ['4'])).
% 0.23/0.50  thf('24', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('25', plain,
% 0.23/0.50      ((((k3_tarski @ sk_B) != (sk_A)))
% 0.23/0.50         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.50  thf('26', plain, (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('sat_resolution*', [status(thm)], ['5', '17'])).
% 0.23/0.50  thf('27', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.23/0.50      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.23/0.50  thf('28', plain, (~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['22', '27'])).
% 0.23/0.50  thf('29', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(dt_k5_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.50  thf('30', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]:
% 0.23/0.50         ((m1_subset_1 @ (k5_setfam_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.23/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.50  thf('32', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('33', plain, ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.23/0.50  thf(t3_subset, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.50  thf('34', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i]:
% 0.23/0.50         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.50  thf('35', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.23/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.50  thf('36', plain, ($false), inference('demod', [status(thm)], ['28', '35'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
