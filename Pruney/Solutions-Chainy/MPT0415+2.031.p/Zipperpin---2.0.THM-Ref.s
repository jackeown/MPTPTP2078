%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EYhvHxeLAl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:13 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 117 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 878 expanded)
%              Number of equality atoms :   23 (  63 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_setfam_1 @ X17 @ ( k7_setfam_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('2',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('6',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ ( sk_D @ X12 @ X14 @ X13 ) ) @ X14 )
      | ( X12
        = ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ( r1_xboole_0 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ sk_B )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('21',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['4','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EYhvHxeLAl
% 0.10/0.31  % Computer   : n015.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 17:13:38 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.31  % Number of cores: 8
% 0.17/0.32  % Python version: Python 3.6.8
% 0.17/0.32  % Running in FO mode
% 0.18/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.54  % Solved by: fo/fo7.sh
% 0.18/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.54  % done 90 iterations in 0.089s
% 0.18/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.54  % SZS output start Refutation
% 0.18/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.54  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.18/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.18/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.18/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.54  thf(t46_setfam_1, conjecture,
% 0.18/0.54    (![A:$i,B:$i]:
% 0.18/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.54       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.18/0.54            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.18/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.54    (~( ![A:$i,B:$i]:
% 0.18/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.54          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.18/0.54               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.18/0.54    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.18/0.54  thf('0', plain,
% 0.18/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.54  thf(involutiveness_k7_setfam_1, axiom,
% 0.18/0.54    (![A:$i,B:$i]:
% 0.18/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.54       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.18/0.54  thf('1', plain,
% 0.18/0.54      (![X16 : $i, X17 : $i]:
% 0.18/0.54         (((k7_setfam_1 @ X17 @ (k7_setfam_1 @ X17 @ X16)) = (X16))
% 0.18/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.18/0.54      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.18/0.54  thf('2', plain,
% 0.18/0.54      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.18/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.54  thf('3', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.18/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.54  thf('4', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.18/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.18/0.54  thf(t4_subset_1, axiom,
% 0.18/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.18/0.54  thf('5', plain,
% 0.18/0.54      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.18/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.54  thf('6', plain,
% 0.18/0.54      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.18/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.54  thf(d8_setfam_1, axiom,
% 0.18/0.54    (![A:$i,B:$i]:
% 0.18/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.54       ( ![C:$i]:
% 0.18/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.18/0.54           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.18/0.54             ( ![D:$i]:
% 0.18/0.54               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.54                 ( ( r2_hidden @ D @ C ) <=>
% 0.18/0.54                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.18/0.54  thf('7', plain,
% 0.18/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.18/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.18/0.54          | (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.18/0.54          | (r2_hidden @ (k3_subset_1 @ X13 @ (sk_D @ X12 @ X14 @ X13)) @ X14)
% 0.18/0.54          | ((X12) = (k7_setfam_1 @ X13 @ X14))
% 0.18/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.18/0.54      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.18/0.54  thf('8', plain,
% 0.18/0.54      (![X0 : $i, X1 : $i]:
% 0.18/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.18/0.54          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ X1))
% 0.18/0.54          | (r2_hidden @ (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.18/0.54             X1)
% 0.18/0.54          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.18/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.54  thf('9', plain,
% 0.18/0.54      (![X0 : $i]:
% 0.18/0.54         ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.18/0.54          | (r2_hidden @ 
% 0.18/0.54             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.18/0.54             k1_xboole_0)
% 0.18/0.54          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.18/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.18/0.54  thf(t48_xboole_1, axiom,
% 0.18/0.54    (![A:$i,B:$i]:
% 0.18/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.18/0.54  thf('10', plain,
% 0.18/0.54      (![X5 : $i, X6 : $i]:
% 0.18/0.54         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.18/0.54           = (k3_xboole_0 @ X5 @ X6))),
% 0.18/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.54  thf(t4_boole, axiom,
% 0.18/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.18/0.54  thf('11', plain,
% 0.18/0.54      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.18/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.18/0.54  thf('12', plain,
% 0.18/0.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.18/0.54  thf(t4_xboole_0, axiom,
% 0.18/0.54    (![A:$i,B:$i]:
% 0.18/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.18/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.18/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.18/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.18/0.54  thf('13', plain,
% 0.18/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.18/0.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.18/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.18/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.18/0.54  thf('14', plain,
% 0.18/0.54      (![X0 : $i, X1 : $i]:
% 0.18/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.18/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.54  thf('15', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.18/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.54  thf('16', plain,
% 0.18/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.54  thf(t43_subset_1, axiom,
% 0.18/0.54    (![A:$i,B:$i]:
% 0.18/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.54       ( ![C:$i]:
% 0.18/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.54           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.18/0.54             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.18/0.54  thf('17', plain,
% 0.18/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.18/0.54         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.18/0.54          | ~ (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.18/0.54          | (r1_xboole_0 @ X10 @ X8)
% 0.18/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.18/0.54      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.18/0.54  thf('18', plain,
% 0.18/0.54      (![X0 : $i]:
% 0.18/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.18/0.54          | (r1_xboole_0 @ X0 @ sk_B)
% 0.18/0.54          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)))),
% 0.18/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.54  thf('19', plain,
% 0.18/0.54      (((r1_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.18/0.54        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.18/0.54      inference('sup-', [status(thm)], ['15', '18'])).
% 0.18/0.54  thf('20', plain,
% 0.18/0.54      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.18/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.18/0.54  thf('21', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_B)),
% 0.18/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.54  thf('22', plain,
% 0.18/0.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.18/0.54  thf('23', plain,
% 0.18/0.54      (![X0 : $i, X1 : $i]:
% 0.18/0.54         ((r1_xboole_0 @ X0 @ X1)
% 0.18/0.54          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.18/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.18/0.54  thf('24', plain,
% 0.18/0.54      (![X0 : $i]:
% 0.18/0.54         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.18/0.54          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.18/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.18/0.54  thf('25', plain,
% 0.18/0.54      (![X0 : $i, X1 : $i]:
% 0.18/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.18/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.54  thf('26', plain,
% 0.18/0.54      (![X0 : $i, X1 : $i]:
% 0.18/0.54         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.18/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.54  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.18/0.54      inference('sup-', [status(thm)], ['21', '26'])).
% 0.18/0.54  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.18/0.54      inference('demod', [status(thm)], ['14', '27'])).
% 0.18/0.54  thf('29', plain,
% 0.18/0.54      (![X0 : $i]:
% 0.18/0.54         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.18/0.54          | (r2_hidden @ 
% 0.18/0.54             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.18/0.54             k1_xboole_0))),
% 0.18/0.54      inference('clc', [status(thm)], ['9', '28'])).
% 0.18/0.54  thf('30', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.18/0.54      inference('demod', [status(thm)], ['14', '27'])).
% 0.18/0.54  thf('31', plain,
% 0.18/0.54      (![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.18/0.54      inference('clc', [status(thm)], ['29', '30'])).
% 0.18/0.54  thf('32', plain, (((k1_xboole_0) = (sk_B))),
% 0.18/0.54      inference('demod', [status(thm)], ['4', '31'])).
% 0.18/0.54  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.18/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.54  thf('34', plain, ($false),
% 0.18/0.54      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.18/0.54  
% 0.18/0.54  % SZS output end Refutation
% 0.18/0.54  
% 0.18/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
