%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KoZE17d5PD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:25 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  538 ( 940 expanded)
%              Number of equality atoms :   46 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ ( k1_setfam_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_4 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = ( k6_setfam_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_4 )
      = ( k6_setfam_1 @ sk_A @ sk_C_4 ) )
    | ( sk_C_4 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k6_setfam_1 @ X24 @ X23 )
        = ( k1_setfam_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_4 )
    = ( k1_setfam_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_4 )
      = ( k1_setfam_1 @ sk_C_4 ) )
    | ( sk_C_4 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = ( k6_setfam_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k6_setfam_1 @ X24 @ X23 )
        = ( k1_setfam_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_4 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C_4 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X16 @ X17 ) @ X16 )
      | ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_2 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_B @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_4 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_2 @ sk_B ) @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X9 )
        = X9 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ sk_C_4 )
      = sk_C_4 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('38',plain,
    ( ( sk_C_4 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_4 ) @ ( k1_setfam_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','38'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['3','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('42',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ( ( k8_setfam_1 @ X20 @ k1_xboole_0 )
        = X20 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('43',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( k8_setfam_1 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('47',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40','44','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KoZE17d5PD
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 274 iterations in 0.117s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.38/0.57  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.38/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(t59_setfam_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57           ( ( r1_tarski @ B @ C ) =>
% 0.38/0.57             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i]:
% 0.38/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57          ( ![C:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57              ( ( r1_tarski @ B @ C ) =>
% 0.38/0.57                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_4) @ 
% 0.38/0.57          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain, ((r1_tarski @ sk_B @ sk_C_4)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t7_setfam_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X31 : $i, X32 : $i]:
% 0.38/0.57         (((X31) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X31 @ X32)
% 0.38/0.57          | (r1_tarski @ (k1_setfam_1 @ X32) @ (k1_setfam_1 @ X31)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (((r1_tarski @ (k1_setfam_1 @ sk_C_4) @ (k1_setfam_1 @ sk_B))
% 0.38/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d10_setfam_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.38/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (((X19) = (k1_xboole_0))
% 0.38/0.57          | ((k8_setfam_1 @ X20 @ X19) = (k6_setfam_1 @ X20 @ X19))
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_4) = (k6_setfam_1 @ sk_A @ sk_C_4))
% 0.38/0.57        | ((sk_C_4) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k6_setfam_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X23 : $i, X24 : $i]:
% 0.38/0.57         (((k6_setfam_1 @ X24 @ X23) = (k1_setfam_1 @ X23))
% 0.38/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.57  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C_4) = (k1_setfam_1 @ sk_C_4))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_4) = (k1_setfam_1 @ sk_C_4))
% 0.38/0.57        | ((sk_C_4) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['6', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (((X19) = (k1_xboole_0))
% 0.38/0.57          | ((k8_setfam_1 @ X20 @ X19) = (k6_setfam_1 @ X20 @ X19))
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.38/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X23 : $i, X24 : $i]:
% 0.38/0.57         (((k6_setfam_1 @ X24 @ X23) = (k1_setfam_1 @ X23))
% 0.38/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.57  thf('16', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.38/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['13', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_4) @ 
% 0.38/0.57          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_4) @ (k1_setfam_1 @ sk_B))
% 0.38/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_4) @ (k1_setfam_1 @ sk_B))
% 0.38/0.57        | ((sk_C_4) = (k1_xboole_0))
% 0.38/0.57        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '19'])).
% 0.38/0.57  thf(d3_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.57  thf(t3_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X25 : $i, X27 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.57  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf(t10_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.57            ( ![C:$i]:
% 0.38/0.57              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_C_3 @ X16 @ X17) @ X16)
% 0.38/0.57          | ((X16) = (k1_xboole_0))
% 0.38/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_3 @ X0 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf(t7_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ~( ( r2_hidden @ A @ B ) & 
% 0.38/0.57          ( ![C:$i]:
% 0.38/0.57            ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.57                 ( ![D:$i]:
% 0.38/0.57                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X13 @ X14) | (r2_hidden @ (sk_C_2 @ X14) @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf('31', plain, ((r1_tarski @ sk_B @ sk_C_4)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.57          | (r2_hidden @ X0 @ X2)
% 0.38/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_4) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((((sk_B) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ sk_B) @ sk_C_4))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '33'])).
% 0.38/0.57  thf(t46_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.57       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         (((k2_xboole_0 @ (k1_tarski @ X10) @ X9) = (X9))
% 0.38/0.57          | ~ (r2_hidden @ X10 @ X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      ((((sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_xboole_0 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ sk_C_4) = (sk_C_4)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf(t49_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.57  thf('38', plain, ((((sk_C_4) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      ((((sk_B) = (k1_xboole_0))
% 0.38/0.57        | ~ (r1_tarski @ (k1_setfam_1 @ sk_C_4) @ (k1_setfam_1 @ sk_B)))),
% 0.38/0.57      inference('clc', [status(thm)], ['20', '38'])).
% 0.38/0.57  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.57      inference('clc', [status(thm)], ['3', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (((X19) != (k1_xboole_0))
% 0.38/0.57          | ((k8_setfam_1 @ X20 @ X19) = (X20))
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X20 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20)))
% 0.38/0.57          | ((k8_setfam_1 @ X20 @ k1_xboole_0) = (X20)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.57  thf(t4_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf('44', plain, (![X20 : $i]: ((k8_setfam_1 @ X20 @ k1_xboole_0) = (X20))),
% 0.38/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k8_setfam_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i]:
% 0.38/0.57         ((m1_subset_1 @ (k8_setfam_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.38/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_4) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X25 : $i, X26 : $i]:
% 0.38/0.57         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.57  thf('49', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_4) @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf('50', plain, ($false),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '40', '44', '49'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
