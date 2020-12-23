%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.URvVbSDsIl

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 118 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 ( 960 expanded)
%              Number of equality atoms :   27 (  77 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( m1_setfam_1 @ X11 @ X10 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( ( k5_setfam_1 @ X16 @ X15 )
        = ( k3_tarski @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_setfam_1 @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ ( k3_tarski @ X12 ) ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('32',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['28','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.URvVbSDsIl
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 51 iterations in 0.018s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.46  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(t60_setfam_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46          ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t60_setfam_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)) | (m1_setfam_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (((m1_setfam_1 @ sk_B @ sk_A)) <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf(d12_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i]:
% 0.21/0.46         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (m1_setfam_1 @ X11 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (((r1_tarski @ sk_A @ (k3_tarski @ sk_B)))
% 0.21/0.46         <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)) | ~ (m1_setfam_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))) | 
% 0.21/0.46       ~ ((m1_setfam_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('split', [status(esa)], ['4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k5_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X15 : $i, X16 : $i]:
% 0.21/0.46         (((k5_setfam_1 @ X16 @ X15) = (k3_tarski @ X15))
% 0.21/0.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.21/0.46  thf('8', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))
% 0.21/0.46         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((k3_tarski @ sk_B) = (sk_A)))
% 0.21/0.46         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.46      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf(d10_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('12', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X10 : $i, X12 : $i]:
% 0.21/0.46         ((m1_setfam_1 @ X12 @ X10) | ~ (r1_tarski @ X10 @ (k3_tarski @ X12)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.46  thf('14', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (((m1_setfam_1 @ sk_B @ sk_A))
% 0.21/0.46         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.46      inference('sup+', [status(thm)], ['10', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      ((~ (m1_setfam_1 @ sk_B @ sk_A)) <= (~ ((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['4'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (((m1_setfam_1 @ sk_B @ sk_A)) | 
% 0.21/0.46       ~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (((m1_setfam_1 @ sk_B @ sk_A)) | (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('19', plain, (((m1_setfam_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['5', '17', '18'])).
% 0.21/0.46  thf('20', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['3', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X4 : $i, X6 : $i]:
% 0.21/0.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)
% 0.21/0.46        | ((k3_tarski @ sk_B) = (sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)))
% 0.21/0.46         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['4'])).
% 0.21/0.46  thf('24', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      ((((k3_tarski @ sk_B) != (sk_A)))
% 0.21/0.46         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain, (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['5', '17'])).
% 0.21/0.46  thf('27', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.21/0.46  thf('28', plain, (~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['22', '27'])).
% 0.21/0.46  thf(d3_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]:
% 0.21/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(dt_k5_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (k5_setfam_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.21/0.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.46  thf('33', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('34', plain, ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.47  thf(l3_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.47          | (r2_hidden @ X7 @ X9)
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k3_tarski @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k3_tarski @ sk_B) @ X0)
% 0.21/0.47          | (r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_B)) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)
% 0.21/0.47        | (r1_tarski @ (k3_tarski @ sk_B) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.47  thf('40', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.21/0.47      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.47  thf('41', plain, ($false), inference('demod', [status(thm)], ['28', '40'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
