%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Q8RE7s2tf

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 102 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  583 (1029 expanded)
%              Number of equality atoms :   48 (  83 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t48_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t47_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) )
          = ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X20 @ ( k2_subset_1 @ X20 ) @ ( k5_setfam_1 @ X20 @ X19 ) )
        = ( k6_setfam_1 @ X20 @ ( k7_setfam_1 @ X20 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t47_setfam_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k7_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X20 @ ( k5_setfam_1 @ X20 @ X19 ) )
        = ( k6_setfam_1 @ X20 @ ( k7_setfam_1 @ X20 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_setfam_1 @ X16 @ ( k7_setfam_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('22',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_setfam_1 @ X17 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('34',plain,(
    m1_subset_1 @ ( k6_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k7_subset_1 @ sk_A @ ( k2_subset_1 @ sk_A ) @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k7_subset_1 @ sk_A @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('42',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Q8RE7s2tf
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 100 iterations in 0.075s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.53  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(t48_setfam_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.53           ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.53              ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t48_setfam_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k7_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.20/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(dt_k5_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k5_setfam_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ 
% 0.20/0.53         (k3_subset_1 @ sk_A @ 
% 0.20/0.53          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.20/0.53         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ 
% 0.20/0.53         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         = (k4_xboole_0 @ sk_A @ 
% 0.20/0.53            (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(t47_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53         ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) ) =
% 0.20/0.53           ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((X19) = (k1_xboole_0))
% 0.20/0.53          | ((k7_subset_1 @ X20 @ (k2_subset_1 @ X20) @ 
% 0.20/0.53              (k5_setfam_1 @ X20 @ X19))
% 0.20/0.53              = (k6_setfam_1 @ X20 @ (k7_setfam_1 @ X20 @ X19)))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.20/0.53      inference('cnf', [status(esa)], [t47_setfam_1])).
% 0.20/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.53  thf('12', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf(dt_k2_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.53  thf('14', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('15', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.53          | ((k7_subset_1 @ X7 @ X6 @ X8) = (k4_xboole_0 @ X6 @ X8)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((X19) = (k1_xboole_0))
% 0.20/0.53          | ((k4_xboole_0 @ X20 @ (k5_setfam_1 @ X20 @ X19))
% 0.20/0.53              = (k6_setfam_1 @ X20 @ (k7_setfam_1 @ X20 @ X19)))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_A @ 
% 0.20/0.53          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53          = (k6_setfam_1 @ sk_A @ 
% 0.20/0.53             (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.20/0.53        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(involutiveness_k7_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (((k7_setfam_1 @ X16 @ (k7_setfam_1 @ X16 @ X15)) = (X15))
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_A @ 
% 0.20/0.53          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53          = (k6_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t46_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         (((k7_setfam_1 @ X17 @ X18) != (k1_xboole_0))
% 0.20/0.53          | ((X18) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.20/0.53      inference('cnf', [status(esa)], [t46_setfam_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain, (((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ 
% 0.20/0.53         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ 
% 0.20/0.53         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.53         = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k6_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k6_setfam_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_setfam_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53         = (k4_xboole_0 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53         != (k7_subset_1 @ sk_A @ (k2_subset_1 @ sk_A) @ 
% 0.20/0.53             (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53         != (k7_subset_1 @ sk_A @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.53         != (k4_xboole_0 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['37', '42'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
