%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I6Wx4P6ZtP

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 246 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  359 (1861 expanded)
%              Number of equality atoms :   22 ( 118 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t10_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k4_tarski @ ( sk_C @ X18 ) @ ( sk_D_1 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k4_tarski @ ( sk_C @ X0 ) @ ( sk_D_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('22',plain,(
    ! [X26: $i,X28: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X26 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('23',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_D_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['32','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I6Wx4P6ZtP
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:58:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 158 iterations in 0.107s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(t10_mcart_1, conjecture,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.57       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.57        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.57          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.57            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t10_mcart_1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)
% 0.20/0.57        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))
% 0.20/0.57         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('3', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(l1_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X7 : $i, X9 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf(t3_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X15 : $i, X17 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      ((m1_subset_1 @ (k1_tarski @ sk_A) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf(cc1_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( v1_relat_1 @ C ) ))).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.57         ((v1_relat_1 @ X23)
% 0.20/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.57  thf('9', plain, ((v1_relat_1 @ (k1_tarski @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf(t69_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('10', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf(d2_tarski, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (((X1) != (X0))
% 0.20/0.57          | (r2_hidden @ X1 @ X2)
% 0.20/0.57          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.57  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['10', '12'])).
% 0.20/0.57  thf(d1_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.57              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i]:
% 0.20/0.57         (((X18) = (k4_tarski @ (sk_C @ X18) @ (sk_D_1 @ X18)))
% 0.20/0.57          | ~ (r2_hidden @ X18 @ X19)
% 0.20/0.57          | ~ (v1_relat_1 @ X19))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ (k1_tarski @ X0))
% 0.20/0.57          | ((X0) = (k4_tarski @ (sk_C @ X0) @ (sk_D_1 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('16', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D_1 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.57  thf('17', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D_1 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.57  thf(t7_mcart_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.57       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X26 : $i, X27 : $i]: ((k1_mcart_1 @ (k4_tarski @ X26 @ X27)) = (X26))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.57  thf('19', plain, (((k1_mcart_1 @ sk_A) = (sk_C @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_D_1 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_D_1 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X26 : $i, X28 : $i]: ((k2_mcart_1 @ (k4_tarski @ X26 @ X28)) = (X28))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.57  thf('23', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1 @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.57  thf(l54_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.57         ((r2_hidden @ X10 @ X11)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.57          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('27', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '26'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))
% 0.20/0.57         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('29', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)) | 
% 0.20/0.57       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('31', plain, (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.20/0.57  thf('32', plain, (~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.20/0.57  thf('33', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.57         ((r2_hidden @ X12 @ X13)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.57          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.57  thf('37', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.20/0.57      inference('sup-', [status(thm)], ['33', '36'])).
% 0.20/0.57  thf('38', plain, ($false), inference('demod', [status(thm)], ['32', '37'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
