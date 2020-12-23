%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzdSjsEiMC

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  92 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  384 ( 725 expanded)
%              Number of equality atoms :   23 (  59 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_setfam_1 @ X15 @ ( k7_setfam_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('15',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( X10
       != ( k7_setfam_1 @ X11 @ X12 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X11 @ X13 ) @ X12 )
      | ~ ( r2_hidden @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k7_setfam_1 @ X11 @ X12 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X11 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['26','29'])).

thf('31',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzdSjsEiMC
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 79 iterations in 0.044s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(d5_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.49         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X6 : $i, X8 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.49  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('condensation', [status(thm)], ['8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.49          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.49          | ((X1) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf(t46_setfam_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(involutiveness_k7_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (((k7_setfam_1 @ X15 @ (k7_setfam_1 @ X15 @ X14)) = (X14))
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.20/0.49      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(d8_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.49             ( ![D:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.20/0.49          | ((X10) != (k7_setfam_1 @ X11 @ X12))
% 0.20/0.49          | (r2_hidden @ (k3_subset_1 @ X11 @ X13) @ X12)
% 0.20/0.49          | ~ (r2_hidden @ X13 @ X10)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11))
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11))
% 0.20/0.49          | ~ (r2_hidden @ X13 @ (k7_setfam_1 @ X11 @ X12))
% 0.20/0.49          | (r2_hidden @ (k3_subset_1 @ X11 @ X13) @ X12)
% 0.20/0.49          | ~ (m1_subset_1 @ (k7_setfam_1 @ X11 @ X12) @ 
% 0.20/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.49          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.49  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('condensation', [status(thm)], ['8'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X19 @ X20)
% 0.20/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.20/0.49          | (m1_subset_1 @ X19 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.20/0.49      inference('clc', [status(thm)], ['26', '29'])).
% 0.20/0.49  thf('31', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '30'])).
% 0.20/0.49  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
