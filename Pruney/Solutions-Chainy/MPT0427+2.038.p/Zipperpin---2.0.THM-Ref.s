%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bHtlvdP2mj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:25 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   76 (  96 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  517 ( 900 expanded)
%              Number of equality atoms :   51 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = ( k6_setfam_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k6_setfam_1 @ sk_A @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_2 )
    = ( k1_setfam_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k1_setfam_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = ( k6_setfam_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('13',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_tarski @ ( k1_setfam_1 @ X27 ) @ ( k1_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','26'])).

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

thf('28',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','36'])).

thf('38',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('40',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
        = X15 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('45',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38','42','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bHtlvdP2mj
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:38:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 173 iterations in 0.095s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(t59_setfam_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55           ( ( r1_tarski @ B @ C ) =>
% 0.37/0.55             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55          ( ![C:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55              ( ( r1_tarski @ B @ C ) =>
% 0.37/0.55                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.37/0.55          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d10_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.55           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.37/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i]:
% 0.37/0.55         (((X14) = (k1_xboole_0))
% 0.37/0.55          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.37/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k6_setfam_1 @ sk_A @ sk_C_2))
% 0.37/0.55        | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k6_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.37/0.55  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))
% 0.37/0.55        | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['3', '6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i]:
% 0.37/0.55         (((X14) = (k1_xboole_0))
% 0.37/0.55          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.37/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.37/0.55  thf('13', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.37/0.55          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.37/0.55        | ((sk_C_2) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '16'])).
% 0.37/0.55  thf('18', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t7_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.37/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.55         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X26 : $i, X27 : $i]:
% 0.37/0.55         (((X26) = (k1_xboole_0))
% 0.37/0.55          | ~ (r1_tarski @ X26 @ X27)
% 0.37/0.55          | (r1_tarski @ (k1_setfam_1 @ X27) @ (k1_setfam_1 @ X26)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (((r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.55  thf('21', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('clc', [status(thm)], ['17', '20'])).
% 0.37/0.55  thf(t7_xboole_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('24', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d3_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '26'])).
% 0.37/0.55  thf(t3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.55          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((sk_B_1) = (k1_xboole_0))
% 0.37/0.55          | ~ (r1_xboole_0 @ sk_C_2 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (sk_B @ sk_B_1) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ~ (r1_xboole_0 @ sk_C_2 @ sk_B_1)
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((~ (r1_xboole_0 @ sk_C_2 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((~ (r1_xboole_0 @ k1_xboole_0 @ sk_B_1)
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '31'])).
% 0.37/0.55  thf(t4_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.55  thf(t83_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X10 : $i, X12 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.55  thf('37', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '36'])).
% 0.37/0.55  thf('38', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i]:
% 0.37/0.55         (((X14) != (k1_xboole_0))
% 0.37/0.55          | ((k8_setfam_1 @ X15 @ X14) = (X15))
% 0.37/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X15 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.37/0.55          | ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.37/0.55  thf(t4_subset_1, axiom,
% 0.37/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.55  thf('42', plain, (![X15 : $i]: ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15))),
% 0.37/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k8_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k8_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.37/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('47', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('48', plain, ($false),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '38', '42', '47'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
