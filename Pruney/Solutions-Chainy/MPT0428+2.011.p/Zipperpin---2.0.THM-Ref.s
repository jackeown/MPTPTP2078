%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wkyvwhItkD

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 120 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  349 ( 897 expanded)
%              Number of equality atoms :   29 (  74 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ ( k3_tarski @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('8',plain,(
    ~ ( r2_xboole_0 @ sk_A @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A )
    | ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
   <= ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( m1_setfam_1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) )
   <= ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k5_setfam_1 @ X14 @ X13 )
        = ( k3_tarski @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('17',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('19',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_setfam_1 @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ ( k3_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ~ ( m1_setfam_1 @ sk_B @ sk_A )
   <= ~ ( m1_setfam_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
    | ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_setfam_1 @ sk_B @ sk_A )
    | ( ( k5_setfam_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,(
    m1_setfam_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','29','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','31'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( sk_A
      = ( k3_tarski @ sk_B ) )
    | ( r2_xboole_0 @ sk_A @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('37',plain,
    ( ( ( k3_tarski @ sk_B )
     != sk_A )
   <= ( ( k5_setfam_1 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k5_setfam_1 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['14','29'])).

thf('39',plain,(
    ( k3_tarski @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_xboole_0 @ sk_A @ ( k3_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['34','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['8','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wkyvwhItkD
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 65 iterations in 0.021s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.48  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.19/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.19/0.48  thf(t60_setfam_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.48       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.48          ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t60_setfam_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t3_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.48  thf('2', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf(t95_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.48       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i]:
% 0.19/0.48         ((r1_tarski @ (k3_tarski @ X5) @ (k3_tarski @ X6))
% 0.19/0.48          | ~ (r1_tarski @ X5 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf(t99_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.19/0.48  thf('5', plain, (![X7 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X7)) = (X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.19/0.48  thf('6', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf(t60_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.19/0.48  thf('8', plain, (~ (r2_xboole_0 @ sk_A @ (k3_tarski @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)) | (m1_setfam_1 @ sk_B @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (((m1_setfam_1 @ sk_B @ sk_A)) <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf(d12_setfam_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]:
% 0.19/0.48         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (m1_setfam_1 @ X11 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((r1_tarski @ sk_A @ (k3_tarski @ sk_B)))
% 0.19/0.48         <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)) | ~ (m1_setfam_1 @ sk_B @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))) | 
% 0.19/0.48       ~ ((m1_setfam_1 @ sk_B @ sk_A))),
% 0.19/0.48      inference('split', [status(esa)], ['13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k5_setfam_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.48       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         (((k5_setfam_1 @ X14 @ X13) = (k3_tarski @ X13))
% 0.19/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.19/0.48  thf('17', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))
% 0.19/0.48         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((((k3_tarski @ sk_B) = (sk_A)))
% 0.19/0.48         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf(dt_k2_subset_1, axiom,
% 0.19/0.48    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.48  thf('21', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.48  thf('22', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.48  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X10 : $i, X12 : $i]:
% 0.19/0.48         ((m1_setfam_1 @ X12 @ X10) | ~ (r1_tarski @ X10 @ (k3_tarski @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.19/0.48  thf('26', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((m1_setfam_1 @ sk_B @ sk_A))
% 0.19/0.48         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['19', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((~ (m1_setfam_1 @ sk_B @ sk_A)) <= (~ ((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['13'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((m1_setfam_1 @ sk_B @ sk_A)) | 
% 0.19/0.48       ~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (((m1_setfam_1 @ sk_B @ sk_A)) | (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('31', plain, (((m1_setfam_1 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['14', '29', '30'])).
% 0.19/0.48  thf('32', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['12', '31'])).
% 0.19/0.48  thf(d8_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.19/0.48       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i]:
% 0.19/0.48         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((((sk_A) = (k3_tarski @ sk_B))
% 0.19/0.48        | (r2_xboole_0 @ sk_A @ (k3_tarski @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)))
% 0.19/0.48         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['13'])).
% 0.19/0.48  thf('36', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      ((((k3_tarski @ sk_B) != (sk_A)))
% 0.19/0.48         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.48  thf('38', plain, (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['14', '29'])).
% 0.19/0.48  thf('39', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['37', '38'])).
% 0.19/0.48  thf('40', plain, ((r2_xboole_0 @ sk_A @ (k3_tarski @ sk_B))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '39'])).
% 0.19/0.48  thf('41', plain, ($false), inference('demod', [status(thm)], ['8', '40'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
