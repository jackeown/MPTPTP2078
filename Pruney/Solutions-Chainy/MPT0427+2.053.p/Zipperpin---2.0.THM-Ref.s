%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BEgs9BjXs9

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 155 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  670 (1333 expanded)
%              Number of equality atoms :   62 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ X30 )
      | ( r1_tarski @ ( k1_setfam_1 @ X30 ) @ ( k1_setfam_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('13',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('16',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('19',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('23',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('26',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
        = sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('43',plain,(
    ! [X18: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','62'])).

thf('64',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','63'])).

thf('65',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X18: $i] :
      ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('69',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65','66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BEgs9BjXs9
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 274 iterations in 0.103s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.56  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(t59_setfam_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.56             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i]:
% 0.21/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56          ( ![C:$i]:
% 0.21/0.56            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56              ( ( r1_tarski @ B @ C ) =>
% 0.21/0.56                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.56          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t36_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.21/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.56  thf(t85_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.56          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(t7_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.56  thf(t3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.56          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.56          | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.56  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.56  thf('11', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t7_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i]:
% 0.21/0.56         (((X29) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_tarski @ X29 @ X30)
% 0.21/0.56          | (r1_tarski @ (k1_setfam_1 @ X30) @ (k1_setfam_1 @ X29)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d10_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (((X17) = (k1_xboole_0))
% 0.21/0.56          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.21/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i]:
% 0.21/0.56         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.56  thf('19', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.21/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (((X17) = (k1_xboole_0))
% 0.21/0.56          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i]:
% 0.21/0.56         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.56  thf('26', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.56          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.21/0.56        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.56        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '30'])).
% 0.21/0.56  thf('32', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.56  thf('33', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.56          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf(t83_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_1)) = (sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (sk_B_1))
% 0.21/0.56          | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['32', '37'])).
% 0.21/0.56  thf(t4_subset_1, axiom,
% 0.21/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.56  thf(dt_k8_setfam_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.56       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k8_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (((X17) != (k1_xboole_0))
% 0.21/0.56          | ((k8_setfam_1 @ X18 @ X17) = (X18))
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X18 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.21/0.56          | ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.56  thf('45', plain, (![X18 : $i]: ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18))),
% 0.21/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '45'])).
% 0.21/0.56  thf(t3_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.56          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.56          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['52', '59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.56  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['38', '62'])).
% 0.21/0.56  thf('64', plain, ((((k1_xboole_0) = (sk_B_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['10', '63'])).
% 0.21/0.56  thf('65', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.21/0.56      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.56  thf('66', plain, (![X18 : $i]: ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18))),
% 0.21/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k8_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('71', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.56  thf('72', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '65', '66', '71'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
