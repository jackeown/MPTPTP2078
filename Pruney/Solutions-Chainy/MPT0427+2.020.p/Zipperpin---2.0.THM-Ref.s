%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A6rXlyPgu6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:23 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 155 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  571 (1643 expanded)
%              Number of equality atoms :   56 ( 111 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X29 ) @ X29 )
      | ( r1_tarski @ X30 @ ( k1_setfam_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('4',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ X31 @ X33 )
      | ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_B ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ X1 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( sk_C_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( sk_C_1 @ X30 @ X29 ) )
      | ( r1_tarski @ X30 @ ( k1_setfam_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('18',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k6_setfam_1 @ sk_A @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('21',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_2 )
    = ( k1_setfam_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k1_setfam_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('25',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('28',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','32'])).

thf('34',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('36',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_C_2 = sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('45',plain,(
    ! [X18: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X18: $i] :
      ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('50',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43','47','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A6rXlyPgu6
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 352 iterations in 0.161s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.41/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.41/0.62  thf(t59_setfam_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62           ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62          ( ![C:$i]:
% 0.41/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62              ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.41/0.62          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d10_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.41/0.62  thf(t6_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.41/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X29 : $i, X30 : $i]:
% 0.41/0.62         (((X29) = (k1_xboole_0))
% 0.41/0.62          | (r2_hidden @ (sk_C_1 @ X30 @ X29) @ X29)
% 0.41/0.62          | (r1_tarski @ X30 @ (k1_setfam_1 @ X29)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.41/0.62  thf('4', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t3_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X23 : $i, X25 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.62  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C_2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf(l3_subset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X13 @ X14)
% 0.41/0.62          | (r2_hidden @ X13 @ X15)
% 0.41/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_B))
% 0.41/0.62          | ((sk_B) = (k1_xboole_0))
% 0.41/0.62          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_C_2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['3', '8'])).
% 0.41/0.62  thf(t8_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.41/0.62       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X31 @ X32)
% 0.41/0.62          | ~ (r1_tarski @ X31 @ X33)
% 0.41/0.62          | (r1_tarski @ (k1_setfam_1 @ X32) @ X33))),
% 0.41/0.62      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (((sk_B) = (k1_xboole_0))
% 0.41/0.62          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_B))
% 0.41/0.62          | (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ X1)
% 0.41/0.62          | ~ (r1_tarski @ (sk_C_1 @ X0 @ sk_B) @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (sk_C_1 @ X0 @ sk_B))
% 0.41/0.62          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_B))
% 0.41/0.62          | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '11'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X29 : $i, X30 : $i]:
% 0.41/0.62         (((X29) = (k1_xboole_0))
% 0.41/0.62          | ~ (r1_tarski @ X30 @ (sk_C_1 @ X30 @ X29))
% 0.41/0.62          | (r1_tarski @ X30 @ (k1_setfam_1 @ X29)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0))
% 0.41/0.62        | (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B))
% 0.41/0.62        | (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (((r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d10_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         (((X17) = (k1_xboole_0))
% 0.41/0.62          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k6_setfam_1 @ sk_A @ sk_C_2))
% 0.41/0.62        | ((sk_C_2) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k6_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i]:
% 0.41/0.62         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.41/0.62  thf('21', plain, (((k6_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))
% 0.41/0.62        | ((sk_C_2) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['18', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         (((X17) = (k1_xboole_0))
% 0.41/0.62          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i]:
% 0.41/0.62         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.41/0.62  thf('28', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['25', '28'])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.41/0.62          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_setfam_1 @ sk_B))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B))
% 0.41/0.62        | ((sk_C_2) = (k1_xboole_0))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_C_2) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['15', '32'])).
% 0.41/0.62  thf('34', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.41/0.62  thf('35', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.41/0.62  thf('36', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X0 : $i, X2 : $i]:
% 0.41/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('38', plain, ((~ (r1_tarski @ sk_C_2 @ sk_B) | ((sk_C_2) = (sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      ((~ (r1_tarski @ k1_xboole_0 @ sk_B)
% 0.41/0.62        | ((sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_C_2) = (sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['35', '38'])).
% 0.41/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.62  thf('40', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.62  thf('41', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      ((((k1_xboole_0) = (sk_B))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['34', '41'])).
% 0.41/0.62  thf('43', plain, (((k1_xboole_0) = (sk_B))),
% 0.41/0.62      inference('simplify', [status(thm)], ['42'])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         (((X17) != (k1_xboole_0))
% 0.41/0.62          | ((k8_setfam_1 @ X18 @ X17) = (X18))
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X18 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.41/0.62          | ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.62  thf(t4_subset_1, axiom,
% 0.41/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.62  thf('47', plain, (![X18 : $i]: ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18))),
% 0.41/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k8_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k8_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.41/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i]:
% 0.41/0.62         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.62  thf('52', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.62  thf('53', plain, ($false),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '43', '47', '52'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
