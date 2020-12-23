%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DUDnY6zlQW

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
% Statistics : Number of formulae       :   63 ( 195 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 (1647 expanded)
%              Number of equality atoms :   30 ( 143 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ ( k3_tarski @ X6 ) )
      | ~ ( m1_setfam_1 @ X6 @ X5 ) ) ),
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
    ! [X5: $i,X7: $i] :
      ( ( m1_setfam_1 @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k3_tarski @ X7 ) ) ) ),
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
    r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','19'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k3_tarski @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ( k3_tarski @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['25','26'])).

thf('35',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( sk_C @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ ( sk_C @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('43',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['28','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DUDnY6zlQW
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 80 iterations in 0.047s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(t60_setfam_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.54       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.54          ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t60_setfam_1])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)) | (m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (((m1_setfam_1 @ sk_B @ sk_A)) <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf(d12_setfam_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X5 : $i, X6 : $i]:
% 0.22/0.54         ((r1_tarski @ X5 @ (k3_tarski @ X6)) | ~ (m1_setfam_1 @ X6 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (((r1_tarski @ sk_A @ (k3_tarski @ sk_B)))
% 0.22/0.54         <= (((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)) | ~ (m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))) | 
% 0.22/0.54       ~ ((m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k5_setfam_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.54       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.22/0.54  thf('8', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))
% 0.22/0.54         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((((k3_tarski @ sk_B) = (sk_A)))
% 0.22/0.54         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X5 : $i, X7 : $i]:
% 0.22/0.54         ((m1_setfam_1 @ X7 @ X5) | ~ (r1_tarski @ X5 @ (k3_tarski @ X7)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.22/0.54  thf('14', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (((m1_setfam_1 @ sk_B @ sk_A))
% 0.22/0.54         <= ((((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['10', '14'])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((~ (m1_setfam_1 @ sk_B @ sk_A)) <= (~ ((m1_setfam_1 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (((m1_setfam_1 @ sk_B @ sk_A)) | 
% 0.22/0.54       ~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (((m1_setfam_1 @ sk_B @ sk_A)) | (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf('19', plain, (((m1_setfam_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['5', '17', '18'])).
% 0.22/0.54  thf('20', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['3', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      ((~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)
% 0.22/0.54        | ((k3_tarski @ sk_B) = (sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((((k5_setfam_1 @ sk_A @ sk_B) != (sk_A)))
% 0.22/0.54         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf('24', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      ((((k3_tarski @ sk_B) != (sk_A)))
% 0.22/0.54         <= (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf('26', plain, (~ (((k5_setfam_1 @ sk_A @ sk_B) = (sk_A)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['5', '17'])).
% 0.22/0.54  thf('27', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('28', plain, (~ (r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['22', '27'])).
% 0.22/0.54  thf('29', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['3', '19'])).
% 0.22/0.54  thf(t94_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.22/0.54       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.22/0.54          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ (k3_tarski @ X1))
% 0.22/0.54          | ((X0) = (k3_tarski @ X1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((((sk_A) = (k3_tarski @ sk_B))
% 0.22/0.54        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['29', '32'])).
% 0.22/0.54  thf('34', plain, (((k3_tarski @ sk_B) != (sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('35', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t4_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X13 @ X14)
% 0.22/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.54          | (m1_subset_1 @ X13 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['35', '38'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('41', plain, ((r1_tarski @ (sk_C @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.22/0.54          | ~ (r1_tarski @ (sk_C @ X4 @ X3) @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.22/0.54  thf('43', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf('44', plain, ($false), inference('demod', [status(thm)], ['28', '43'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
