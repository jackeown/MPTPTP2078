%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4L734hNs1e

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 150 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  494 (1568 expanded)
%              Number of equality atoms :   47 ( 102 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
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
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('16',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_C )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('31',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['20','31'])).

thf('33',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['3','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['3','32'])).

thf('37',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('39',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( ( k8_setfam_1 @ X16 @ k1_xboole_0 )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('43',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['34','40','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4L734hNs1e
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 120 iterations in 0.073s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t59_setfam_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.52             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52              ( ( r1_tarski @ B @ C ) =>
% 0.20/0.52                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.20/0.52          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t7_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i]:
% 0.20/0.52         (((X24) = (k1_xboole_0))
% 0.20/0.52          | ~ (r1_tarski @ X24 @ X25)
% 0.20/0.52          | (r1_tarski @ (k1_setfam_1 @ X25) @ (k1_setfam_1 @ X24)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.20/0.52        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d10_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((X15) = (k1_xboole_0))
% 0.20/0.52          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.20/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.52  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.20/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((X15) = (k1_xboole_0))
% 0.20/0.52          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.20/0.52        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.52  thf('16', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.20/0.52        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.20/0.52          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.20/0.52        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.20/0.52        | ((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '19'])).
% 0.20/0.52  thf('21', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t7_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.52  thf(l1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X10 : $i, X12 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf(t1_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.52       ( r1_tarski @ A @ C ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.52          | ~ (r1_tarski @ X6 @ X7)
% 0.20/0.52          | (r1_tarski @ X5 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_C)
% 0.20/0.52        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '26'])).
% 0.20/0.52  thf(t12_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.52        | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_C) = (sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf(t49_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k1_tarski @ X13) @ X14) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.52  thf('31', plain, ((((sk_C) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.52        | ~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1)))),
% 0.20/0.52      inference('clc', [status(thm)], ['20', '31'])).
% 0.20/0.52  thf('33', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['3', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.20/0.52          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['3', '32'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((X15) != (k1_xboole_0))
% 0.20/0.52          | ((k8_setfam_1 @ X16 @ X15) = (X16))
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.20/0.52          | ((k8_setfam_1 @ X16 @ k1_xboole_0) = (X16)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.52  thf('40', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k8_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k8_setfam_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('45', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '40', '45'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
