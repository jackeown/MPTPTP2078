%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R9Upm3vvkh

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 146 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  528 (1245 expanded)
%              Number of equality atoms :   42 (  76 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X8 @ X7 )
        = ( k6_setfam_1 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k6_setfam_1 @ X12 @ X11 )
        = ( k1_setfam_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X8 @ X7 )
        = ( k6_setfam_1 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k6_setfam_1 @ X12 @ X11 )
        = ( k1_setfam_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('13',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ ( k1_setfam_1 @ X17 ) @ ( k1_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X8 @ X7 )
        = X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('24',plain,(
    ! [X8: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) )
      | ( ( k8_setfam_1 @ X8 @ k1_xboole_0 )
        = X8 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( ( k8_setfam_1 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','28'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i] :
      ( ( k8_setfam_1 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X8: $i] :
      ( ( k8_setfam_1 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('58',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54','55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R9Upm3vvkh
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 156 iterations in 0.102s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(t59_setfam_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.55             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55          ( ![C:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55              ( ( r1_tarski @ B @ C ) =>
% 0.21/0.55                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d10_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.55           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (((X7) = (k1_xboole_0))
% 0.21/0.55          | ((k8_setfam_1 @ X8 @ X7) = (k6_setfam_1 @ X8 @ X7))
% 0.21/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.21/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (((k6_setfam_1 @ X12 @ X11) = (k1_setfam_1 @ X11))
% 0.21/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.55  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.21/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (((X7) = (k1_xboole_0))
% 0.21/0.55          | ((k8_setfam_1 @ X8 @ X7) = (k6_setfam_1 @ X8 @ X7))
% 0.21/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (((k6_setfam_1 @ X12 @ X11) = (k1_setfam_1 @ X11))
% 0.21/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.55  thf('13', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.55        | ((sk_C) = (k1_xboole_0))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '16'])).
% 0.21/0.55  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t7_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (((X16) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X16 @ X17)
% 0.21/0.55          | (r1_tarski @ (k1_setfam_1 @ X17) @ (k1_setfam_1 @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['17', '20'])).
% 0.21/0.55  thf(l13_xboole_0, axiom,
% 0.21/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         (((X7) != (k1_xboole_0))
% 0.21/0.56          | ((k8_setfam_1 @ X8 @ X7) = (X8))
% 0.21/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X8 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8)))
% 0.21/0.56          | ((k8_setfam_1 @ X8 @ k1_xboole_0) = (X8)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('25', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf(t3_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X13 : $i, X15 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain, (![X8 : $i]: ((k8_setfam_1 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.56      inference('demod', [status(thm)], ['24', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '28'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.56        | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.21/0.56        | ~ (v1_xboole_0 @ sk_C)
% 0.21/0.56        | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.56  thf('34', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.56  thf('36', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.56  thf(t69_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ X3 @ X4)
% 0.21/0.56          | ~ (r1_tarski @ X3 @ X4)
% 0.21/0.56          | (v1_xboole_0 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.56  thf('40', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '39'])).
% 0.21/0.56  thf('41', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['33', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf(dt_k8_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k8_setfam_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain, (![X8 : $i]: ((k8_setfam_1 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.56      inference('demod', [status(thm)], ['24', '27'])).
% 0.21/0.56  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '49'])).
% 0.21/0.56  thf('51', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['50', '53'])).
% 0.21/0.56  thf('55', plain, (![X8 : $i]: ((k8_setfam_1 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.56      inference('demod', [status(thm)], ['24', '27'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k8_setfam_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('60', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.56  thf('61', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '54', '55', '60'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
