%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s5O5oQM7cg

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  499 ( 894 expanded)
%              Number of equality atoms :   42 (  51 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = ( k6_setfam_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('4',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('7',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = ( k6_setfam_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('11',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('14',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ( r1_tarski @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','21'])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','38'])).

thf('40',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('42',plain,(
    ! [X11: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X11: $i] :
      ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('47',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40','44','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s5O5oQM7cg
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 159 iterations in 0.115s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.57  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(t59_setfam_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57       ( ![C:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57           ( ( r1_tarski @ B @ C ) =>
% 0.22/0.57             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57          ( ![C:$i]:
% 0.22/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57              ( ( r1_tarski @ B @ C ) =>
% 0.22/0.57                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.22/0.57          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t7_xboole_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d10_setfam_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.57           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.22/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i]:
% 0.22/0.57         (((X10) = (k1_xboole_0))
% 0.22/0.57          | ((k8_setfam_1 @ X11 @ X10) = (k6_setfam_1 @ X11 @ X10))
% 0.22/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.22/0.57        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k6_setfam_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]:
% 0.22/0.57         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.22/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.22/0.57  thf('7', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.22/0.57        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i]:
% 0.22/0.57         (((X10) = (k1_xboole_0))
% 0.22/0.57          | ((k8_setfam_1 @ X11 @ X10) = (k6_setfam_1 @ X11 @ X10))
% 0.22/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.22/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]:
% 0.22/0.57         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.22/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.22/0.57  thf('14', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.22/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['11', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.22/0.57          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.22/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.22/0.57        | ((sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['8', '17'])).
% 0.22/0.57  thf('19', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t7_setfam_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.57         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X25 : $i, X26 : $i]:
% 0.22/0.57         (((X25) = (k1_xboole_0))
% 0.22/0.57          | ~ (r1_tarski @ X25 @ X26)
% 0.22/0.57          | (r1_tarski @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X25)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.22/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf('22', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.57      inference('clc', [status(thm)], ['18', '21'])).
% 0.22/0.57  thf('23', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t3_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X16 : $i, X18 : $i]:
% 0.22/0.57         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('25', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf(t5_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X22 @ X23)
% 0.22/0.57          | ~ (v1_xboole_0 @ X24)
% 0.22/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57          | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.57          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['22', '27'])).
% 0.22/0.57  thf(t46_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X2)) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.57  thf(t79_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.22/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf(t69_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.57       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         (~ (r1_xboole_0 @ X3 @ X4)
% 0.22/0.57          | ~ (r1_tarski @ X3 @ X4)
% 0.22/0.57          | (v1_xboole_0 @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57          | ~ (r1_tarski @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.57  thf(t4_subset_1, axiom,
% 0.22/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('demod', [status(thm)], ['33', '36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X0 : $i]: (((sk_B_1) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.57      inference('demod', [status(thm)], ['28', '37'])).
% 0.22/0.57  thf('39', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '38'])).
% 0.22/0.57  thf('40', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i]:
% 0.22/0.57         (((X10) != (k1_xboole_0))
% 0.22/0.57          | ((k8_setfam_1 @ X11 @ X10) = (X11))
% 0.22/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X11 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.22/0.57          | ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.57  thf('44', plain, (![X11 : $i]: ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11))),
% 0.22/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(dt_k8_setfam_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.57       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         ((m1_subset_1 @ (k8_setfam_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.22/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      (![X16 : $i, X17 : $i]:
% 0.22/0.57         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('49', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.57  thf('50', plain, ($false),
% 0.22/0.57      inference('demod', [status(thm)], ['0', '40', '44', '49'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
