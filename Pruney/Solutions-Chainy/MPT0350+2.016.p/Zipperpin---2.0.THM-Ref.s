%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R47Gv0PtM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 (  91 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  430 ( 718 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k2_xboole_0 @ X65 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ( r1_tarski @ X52 @ X50 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('20',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['18','20'])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ X11 @ ( sk_D @ X11 @ X10 @ X9 ) )
      | ( X10
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ ( sk_D @ sk_A @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( r1_tarski @ X10 @ ( sk_D @ X11 @ X10 @ X9 ) )
      | ( X10
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('26',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('28',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['18','20'])).

thf('29',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','30'])).

thf('32',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('36',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R47Gv0PtM
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 267 iterations in 0.117s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.54  thf(t25_subset_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.54         ( k2_subset_1 @ A ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.54            ( k2_subset_1 @ A ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.19/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(dt_k3_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (![X62 : $i, X63 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.19/0.54          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.19/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.54  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(d5_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (![X60 : $i, X61 : $i]:
% 0.19/0.54         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.19/0.54          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.54  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.19/0.54          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.19/0.54          | ((k4_subset_1 @ X66 @ X65 @ X67) = (k2_xboole_0 @ X65 @ X67)))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.19/0.54         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.54  thf(t39_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i]:
% 0.19/0.54         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.19/0.54           = (k2_xboole_0 @ X12 @ X13))),
% 0.19/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.54  thf(d10_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.54  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.19/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.54  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(d2_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (![X56 : $i, X57 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X56 @ X57)
% 0.19/0.54          | (r2_hidden @ X56 @ X57)
% 0.19/0.54          | (v1_xboole_0 @ X57))),
% 0.19/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.54        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.54  thf(fc1_subset_1, axiom,
% 0.19/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.54  thf('17', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.54  thf('18', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.54  thf(d1_zfmisc_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X52 @ X51)
% 0.19/0.54          | (r1_tarski @ X52 @ X50)
% 0.19/0.54          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      (![X50 : $i, X52 : $i]:
% 0.19/0.54         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.54  thf('21', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.54      inference('sup-', [status(thm)], ['18', '20'])).
% 0.19/0.54  thf(t14_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.19/0.54         ( ![D:$i]:
% 0.19/0.54           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.19/0.54             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.19/0.54       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X9 @ X10)
% 0.19/0.54          | ~ (r1_tarski @ X11 @ X10)
% 0.19/0.54          | (r1_tarski @ X11 @ (sk_D @ X11 @ X10 @ X9))
% 0.19/0.54          | ((X10) = (k2_xboole_0 @ X9 @ X11)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((sk_A) = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.54          | (r1_tarski @ X0 @ (sk_D @ X0 @ sk_A @ sk_B))
% 0.19/0.54          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (((r1_tarski @ sk_A @ (sk_D @ sk_A @ sk_A @ sk_B))
% 0.19/0.54        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['13', '23'])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X9 @ X10)
% 0.19/0.54          | ~ (r1_tarski @ X11 @ X10)
% 0.19/0.54          | ~ (r1_tarski @ X10 @ (sk_D @ X11 @ X10 @ X9))
% 0.19/0.54          | ((X10) = (k2_xboole_0 @ X9 @ X11)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      ((((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))
% 0.19/0.54        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))
% 0.19/0.54        | ~ (r1_tarski @ sk_A @ sk_A)
% 0.19/0.54        | ~ (r1_tarski @ sk_B @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.54  thf('27', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.19/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.54  thf('28', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.54      inference('sup-', [status(thm)], ['18', '20'])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      ((((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))
% 0.19/0.54        | ((sk_A) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.19/0.54      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.54  thf('30', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['10', '11', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.54         != (k2_subset_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.54  thf('33', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.19/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.54  thf('35', plain,
% 0.19/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.54  thf('37', plain, ($false),
% 0.19/0.54      inference('simplify_reflect-', [status(thm)], ['31', '36'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
