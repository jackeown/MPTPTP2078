%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a1R3Zmxc3S

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:26 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 214 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  599 (1924 expanded)
%              Number of equality atoms :   53 ( 116 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ X6 )
        = X6 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('12',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    r1_tarski @ sk_B_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ ( k1_setfam_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('25',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('28',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('32',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_2 )
      = ( k6_setfam_1 @ sk_A @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('35',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_2 )
    = ( k1_setfam_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_2 )
      = ( k1_setfam_1 @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_2 ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r1_tarski @ sk_B_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','50'])).

thf('55',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('57',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( ( k8_setfam_1 @ X16 @ k1_xboole_0 )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('61',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['52','58','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a1R3Zmxc3S
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 210 iterations in 0.154s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(t59_setfam_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( ![C:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61           ( ( r1_tarski @ B @ C ) =>
% 0.38/0.61             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i]:
% 0.38/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61          ( ![C:$i]:
% 0.38/0.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61              ( ( r1_tarski @ B @ C ) =>
% 0.38/0.61                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.61          (k8_setfam_1 @ sk_A @ sk_B_2))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(existence_m1_subset_1, axiom,
% 0.38/0.61    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.38/0.61  thf('1', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 0.38/0.61      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.38/0.61  thf(t2_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X23 : $i, X24 : $i]:
% 0.38/0.61         ((r2_hidden @ X23 @ X24)
% 0.38/0.61          | (v1_xboole_0 @ X24)
% 0.38/0.61          | ~ (m1_subset_1 @ X23 @ X24))),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B_1 @ X0) @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf(l22_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.61       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]:
% 0.38/0.61         (((k2_xboole_0 @ (k1_tarski @ X7) @ X6) = (X6))
% 0.38/0.61          | ~ (r2_hidden @ X7 @ X6))),
% 0.38/0.61      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X0)
% 0.38/0.61          | ((k2_xboole_0 @ (k1_tarski @ (sk_B_1 @ X0)) @ X0) = (X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf(t49_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X8 : $i, X9 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.61  thf('7', plain, (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.61  thf(t7_xboole_0, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B_1 @ X0) @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.61  thf('12', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 0.38/0.61      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.38/0.61  thf(t5_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X28 @ X29)
% 0.38/0.61          | ~ (v1_xboole_0 @ X30)
% 0.38/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X0)
% 0.38/0.61          | ~ (r2_hidden @ X1 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((sk_B_1 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0))
% 0.38/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['11', '14'])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X0)
% 0.38/0.61          | ~ (r2_hidden @ X1 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.38/0.61          | ~ (v1_xboole_0 @ X0)
% 0.38/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['10', '18'])).
% 0.38/0.61  thf('20', plain, ((r1_tarski @ sk_B_2 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t7_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.61         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X31 : $i, X32 : $i]:
% 0.38/0.61         (((X31) = (k1_xboole_0))
% 0.38/0.61          | ~ (r1_tarski @ X31 @ X32)
% 0.38/0.61          | (r1_tarski @ (k1_setfam_1 @ X32) @ (k1_setfam_1 @ X31)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_2))
% 0.38/0.61        | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(d10_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.61           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.38/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (((X15) = (k1_xboole_0))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.38/0.61        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(redefinition_k6_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.38/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.61  thf('28', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.38/0.61        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['25', '28'])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (((X15) = (k1_xboole_0))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_B_2) = (k6_setfam_1 @ sk_A @ sk_B_2))
% 0.38/0.61        | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.38/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.61  thf('35', plain, (((k6_setfam_1 @ sk_A @ sk_B_2) = (k1_setfam_1 @ sk_B_2))),
% 0.38/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_B_2) = (k1_setfam_1 @ sk_B_2))
% 0.38/0.61        | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.61          (k8_setfam_1 @ sk_A @ sk_B_2))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B_2))
% 0.38/0.61        | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_2))
% 0.38/0.61        | ((sk_C) = (k1_xboole_0))
% 0.38/0.61        | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['29', '38'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      ((((sk_B_2) = (k1_xboole_0))
% 0.38/0.61        | ((sk_B_2) = (k1_xboole_0))
% 0.38/0.61        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['22', '39'])).
% 0.38/0.61  thf('41', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.61  thf('42', plain, ((r1_tarski @ sk_B_2 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t3_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X25 : $i, X27 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('44', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X28 @ X29)
% 0.38/0.61          | ~ (v1_xboole_0 @ X30)
% 0.38/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.38/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.61          | ((sk_B_2) = (k1_xboole_0))
% 0.38/0.61          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.38/0.61      inference('sup-', [status(thm)], ['41', '46'])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X1)
% 0.38/0.61          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.38/0.61          | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['19', '47'])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((sk_B_2) = (k1_xboole_0))
% 0.38/0.61          | ((sk_B_2) = (k1_xboole_0))
% 0.38/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['9', '48'])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B_2) = (k1_xboole_0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.61  thf('51', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['8', '50'])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.38/0.61          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['0', '51'])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('54', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['8', '50'])).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (((X15) != (k1_xboole_0))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ X15) = (X16))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      (![X16 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ k1_xboole_0) = (X16)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.61  thf('58', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['55', '57'])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_k8_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k8_setfam_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.61  thf('62', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i]:
% 0.38/0.61         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('63', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.38/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.61  thf('64', plain, ($false),
% 0.38/0.61      inference('demod', [status(thm)], ['52', '58', '63'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
