%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QYEiyzW1CX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 133 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  423 (1030 expanded)
%              Number of equality atoms :   32 (  85 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('2',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k5_setfam_1 @ X16 @ X15 )
        = ( k3_tarski @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('6',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_setfam_1 @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,
    ( ~ ( m1_setfam_1 @ sk_B @ sk_A )
   <= ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
    | ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
    | ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    m1_setfam_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','15','16'])).

thf('18',plain,(
    m1_setfam_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( m1_setfam_1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

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
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,
    ( ( ( k3_tarski @ sk_B )
     != sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k5_setfam_1 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['3','15'])).

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
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('31',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('33',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    r2_hidden @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['28','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QYEiyzW1CX
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 61 iterations in 0.024s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(t60_setfam_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48          ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t60_setfam_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)) | (m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (((m1_setfam_1 @ sk_B @ sk_A)) <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)) | ~ (m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))) | 
% 0.22/0.48       ~ ((m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k5_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i]:
% 0.22/0.48         (((k5_setfam_1 @ X16 @ X15) = (k3_tarski @ X15))
% 0.22/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.22/0.48  thf('6', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))
% 0.22/0.48         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      ((((k3_tarski @ sk_B) = (sk_A)))
% 0.22/0.48         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(d10_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.48  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.48  thf(d12_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X10 : $i, X12 : $i]:
% 0.22/0.48         ((m1_setfam_1 @ X12 @ X10) | ~ (r1_tarski @ X10 @ (k3_tarski @ X12)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.22/0.48  thf('12', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (((m1_setfam_1 @ sk_B @ sk_A))
% 0.22/0.48         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.48      inference('sup+', [status(thm)], ['8', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((~ (m1_setfam_1 @ sk_B @ sk_A)) <= (~ ((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (((m1_setfam_1 @ sk_B @ sk_A)) | 
% 0.22/0.48       ~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (((m1_setfam_1 @ sk_B @ sk_A)) | (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('17', plain, (((m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['3', '15', '16'])).
% 0.22/0.48  thf('18', plain, ((m1_setfam_1 @ sk_B @ sk_A)),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i]:
% 0.22/0.48         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (m1_setfam_1 @ X11 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.22/0.48  thf('20', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i, X2 : $i]:
% 0.22/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)
% 0.22/0.48        | ((k3_tarski @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)))
% 0.22/0.48         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.48      inference('split', [status(esa)], ['2'])).
% 0.22/0.48  thf('24', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((((k3_tarski @ sk_B) != (sk_A)))
% 0.22/0.48         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain, (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['3', '15'])).
% 0.22/0.48  thf('27', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, (~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['22', '27'])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k5_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (k5_setfam_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.22/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.48  thf('32', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('33', plain, ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.48  thf(t2_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         ((r2_hidden @ X17 @ X18)
% 0.22/0.48          | (v1_xboole_0 @ X18)
% 0.22/0.48          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49        | (r2_hidden @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf(d1_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.49          | (r2_hidden @ X3 @ X5)
% 0.22/0.49          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.49  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['36', '38'])).
% 0.22/0.49  thf(dt_k2_subset_1, axiom,
% 0.22/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.49  thf('41', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('42', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.49  thf(t5_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X19 @ X20)
% 0.22/0.49          | ~ (v1_xboole_0 @ X21)
% 0.22/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.49  thf('45', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['39', '44'])).
% 0.22/0.49  thf('46', plain, ((r2_hidden @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('clc', [status(thm)], ['35', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X6 @ X5)
% 0.22/0.49          | (r1_tarski @ X6 @ X4)
% 0.22/0.49          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X4 : $i, X6 : $i]:
% 0.22/0.49         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['47'])).
% 0.22/0.49  thf('49', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['46', '48'])).
% 0.22/0.49  thf('50', plain, ($false), inference('demod', [status(thm)], ['28', '49'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
