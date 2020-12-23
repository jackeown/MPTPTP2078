%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ODjBuCyXEh

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 117 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  551 (1125 expanded)
%              Number of equality atoms :   54 (  68 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_tarski @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = ( k6_setfam_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = ( k6_setfam_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,
    ( ( k1_xboole_0 != sk_C )
    | ( r1_xboole_0 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,
    ( ( k1_xboole_0 != sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('47',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('49',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) )
      | ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
        = X14 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('54',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47','51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ODjBuCyXEh
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:18:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 177 iterations in 0.065s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(t59_setfam_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.51             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51              ( ( r1_tarski @ B @ C ) =>
% 0.20/0.51                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t7_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         (((X25) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X25 @ X26)
% 0.20/0.51          | (r1_tarski @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X25)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d10_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (((X13) = (k1_xboole_0))
% 0.20/0.51          | ((k8_setfam_1 @ X14 @ X13) = (k6_setfam_1 @ X14 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.51  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (((X13) = (k1_xboole_0))
% 0.20/0.51          | ((k8_setfam_1 @ X14 @ X13) = (k6_setfam_1 @ X14 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.51  thf('16', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '20'])).
% 0.20/0.51  thf('22', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('25', plain, ((r1_tarski @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf(l32_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((k4_xboole_0 @ sk_C @ (k1_zfmisc_1 @ sk_A)) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf(t83_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X9 : $i, X11 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((k1_xboole_0) != (sk_C)) | (r1_xboole_0 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0))
% 0.20/0.51        | (r1_xboole_0 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((r1_xboole_0 @ sk_C @ (k1_zfmisc_1 @ sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.51  thf('32', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t63_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.20/0.51          | ~ (r1_xboole_0 @ X7 @ X8)
% 0.20/0.51          | (r1_xboole_0 @ X6 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('38', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X9 : $i, X11 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((((k1_xboole_0) != (sk_B)) | (r1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain, ((r1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['35', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('45', plain, (((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) = (sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((k4_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('47', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (((X13) != (k1_xboole_0))
% 0.20/0.51          | ((k8_setfam_1 @ X14 @ X13) = (X14))
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X14 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14)))
% 0.20/0.51          | ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.51  thf(t4_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.51  thf('51', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k8_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k8_setfam_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('56', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain, ($false),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '47', '51', '56'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
