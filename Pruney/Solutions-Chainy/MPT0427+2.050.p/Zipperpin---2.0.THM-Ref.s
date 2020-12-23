%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t8kkcWZ4iT

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 100 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  528 ( 949 expanded)
%              Number of equality atoms :   51 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t59_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_tarski @ ( k1_setfam_1 @ X25 ) @ ( k1_setfam_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X13 @ X12 )
        = ( k6_setfam_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k6_setfam_1 @ X17 @ X16 )
        = ( k1_setfam_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X13 @ X12 )
        = ( k6_setfam_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k6_setfam_1 @ X17 @ X16 )
        = ( k1_setfam_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('16',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','39'])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X13 @ X12 )
        = X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('43',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( ( k8_setfam_1 @ X13 @ k1_xboole_0 )
        = X13 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('45',plain,(
    ! [X13: $i] :
      ( ( k8_setfam_1 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('48',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41','45','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t8kkcWZ4iT
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 120 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.51  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(t59_setfam_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.51             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51              ( ( r1_tarski @ B @ C ) =>
% 0.21/0.51                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.51          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t7_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i]:
% 0.21/0.51         (((X24) = (k1_xboole_0))
% 0.21/0.51          | ~ (r1_tarski @ X24 @ X25)
% 0.21/0.51          | (r1_tarski @ (k1_setfam_1 @ X25) @ (k1_setfam_1 @ X24)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d10_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.51           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((X12) = (k1_xboole_0))
% 0.21/0.51          | ((k8_setfam_1 @ X13 @ X12) = (k6_setfam_1 @ X13 @ X12))
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.21/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (((k6_setfam_1 @ X17 @ X16) = (k1_setfam_1 @ X16))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.51  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.21/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((X12) = (k1_xboole_0))
% 0.21/0.51          | ((k8_setfam_1 @ X13 @ X12) = (k6_setfam_1 @ X13 @ X12))
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (((k6_setfam_1 @ X17 @ X16) = (k1_setfam_1 @ X16))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.51  thf('16', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.51          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.21/0.51        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((((sk_B) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0))
% 0.21/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '20'])).
% 0.21/0.51  thf('22', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.51  thf('23', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(l32_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.51  thf('25', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf(t4_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.51  thf(t83_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X8 : $i, X10 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.51  thf(t3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('37', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.51  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '39'])).
% 0.21/0.51  thf('41', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((X12) != (k1_xboole_0))
% 0.21/0.51          | ((k8_setfam_1 @ X13 @ X12) = (X13))
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X13 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.21/0.51          | ((k8_setfam_1 @ X13 @ k1_xboole_0) = (X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.51  thf(t4_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf('45', plain, (![X13 : $i]: ((k8_setfam_1 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k8_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k8_setfam_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.21/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('50', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain, ($false),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '41', '45', '50'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
