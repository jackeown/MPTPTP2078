%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xrA6LnJuHU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 140 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  478 (1293 expanded)
%              Number of equality atoms :   29 ( 117 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X16 @ X15 ) @ X14 )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ ( sk_D @ X14 @ X16 @ X15 ) ) @ X16 )
      | ( X14
        = ( k7_setfam_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_setfam_1 @ X19 @ ( k7_setfam_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('11',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( X14
       != ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['8','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xrA6LnJuHU
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:01 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 60 iterations in 0.034s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.50  thf(t46_setfam_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d8_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.50             ( ![D:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50                 ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X14 @ X16 @ X15) @ X14)
% 0.21/0.50          | (r2_hidden @ (k3_subset_1 @ X15 @ (sk_D @ X14 @ X16 @ X15)) @ X16)
% 0.21/0.50          | ((X14) = (k7_setfam_1 @ X15 @ X16))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.21/0.50          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 0.21/0.50          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.50        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.50           sk_B)
% 0.21/0.50        | ((sk_B) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf('5', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.50        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.50           sk_B)
% 0.21/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.50        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.50           sk_B))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(involutiveness_k7_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i]:
% 0.21/0.50         (((k7_setfam_1 @ X19 @ (k7_setfam_1 @ X19 @ X18)) = (X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.21/0.50      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.21/0.50          | ((X14) != (k7_setfam_1 @ X15 @ X16))
% 0.21/0.50          | (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.21/0.50          | ~ (r2_hidden @ X17 @ X14)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.21/0.50          | ~ (r2_hidden @ X17 @ (k7_setfam_1 @ X15 @ X16))
% 0.21/0.50          | (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ (k7_setfam_1 @ X15 @ X16) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(t4_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('21', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf(t28_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.50           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf(t5_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('26', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf(t64_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.50       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (((X9) != (X11))
% 0.21/0.50          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11))))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['20', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t4_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X20 @ X21)
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.21/0.50          | (m1_subset_1 @ X20 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['31', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['8', '35'])).
% 0.21/0.50  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['31', '34'])).
% 0.21/0.50  thf('38', plain, ($false), inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
