%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYV6x7is8V

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:23 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 222 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  696 (1704 expanded)
%              Number of equality atoms :   65 ( 120 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_tarski @ ( k1_setfam_1 @ X28 ) @ ( k1_setfam_1 @ X27 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['29'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('48',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference('simplify_reflect+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('69',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('72',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( ( k8_setfam_1 @ X16 @ k1_xboole_0 )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k8_setfam_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k8_setfam_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('78',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67','75','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYV6x7is8V
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 330 iterations in 0.157s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
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
% 0.38/0.61      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.61          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t7_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.61         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X27 : $i, X28 : $i]:
% 0.38/0.61         (((X27) = (k1_xboole_0))
% 0.38/0.61          | ~ (r1_tarski @ X27 @ X28)
% 0.38/0.61          | (r1_tarski @ (k1_setfam_1 @ X28) @ (k1_setfam_1 @ X27)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(d10_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.61           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.38/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (((X15) = (k1_xboole_0))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.38/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(redefinition_k6_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.38/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.61  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.38/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['6', '9'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (((X15) = (k1_xboole_0))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.61          (k8_setfam_1 @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.61           (k6_setfam_1 @ sk_A @ sk_B))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.38/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.38/0.61  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['15', '18'])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B))
% 0.38/0.61        | ((sk_C_1) = (k1_xboole_0))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['10', '19'])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      ((((sk_B) = (k1_xboole_0))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0))
% 0.38/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '20'])).
% 0.38/0.61  thf('22', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.61  thf('23', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('25', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.61  thf(l32_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (![X7 : $i, X9 : $i]:
% 0.38/0.61         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.61  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.61  thf(t83_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X12 : $i, X14 : $i]:
% 0.38/0.61         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.61  thf('30', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.61  thf(t69_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.61       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X10 : $i, X11 : $i]:
% 0.38/0.61         (~ (r1_xboole_0 @ X10 @ X11)
% 0.38/0.61          | ~ (r1_tarski @ X10 @ X11)
% 0.38/0.61          | (v1_xboole_0 @ X10))),
% 0.38/0.61      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.61  thf('33', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.61  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.61  thf(d3_tarski, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X1 : $i, X3 : $i]:
% 0.38/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.61  thf('36', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.61  thf(t3_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X21 : $i, X23 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf(t5_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.61         (~ (r2_hidden @ X24 @ X25)
% 0.38/0.61          | ~ (v1_xboole_0 @ X26)
% 0.38/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['35', '40'])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['35', '40'])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X4 : $i, X6 : $i]:
% 0.38/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['41', '44'])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['34', '45'])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['35', '40'])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (![X7 : $i, X9 : $i]:
% 0.38/0.61         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X1) | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (![X12 : $i, X14 : $i]:
% 0.38/0.61         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (((k1_xboole_0) != (X0))
% 0.38/0.61          | ~ (v1_xboole_0 @ X0)
% 0.38/0.61          | (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X1 : $i]:
% 0.38/0.61         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['51'])).
% 0.38/0.61  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.61  thf('54', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.38/0.61      inference('simplify_reflect+', [status(thm)], ['52', '53'])).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      (![X12 : $i, X13 : $i]:
% 0.38/0.61         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.38/0.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i]:
% 0.38/0.61         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.38/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.61  thf('58', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.61  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.61      inference('simplify', [status(thm)], ['58'])).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      (![X4 : $i, X6 : $i]:
% 0.38/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.61  thf('62', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X1 @ X0)
% 0.38/0.61          | ~ (v1_xboole_0 @ X0)
% 0.38/0.61          | ((X1) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['46', '61'])).
% 0.38/0.61  thf('63', plain, ((((sk_B) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['23', '62'])).
% 0.38/0.61  thf('64', plain,
% 0.38/0.61      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.61        | ((sk_B) = (k1_xboole_0))
% 0.38/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['22', '63'])).
% 0.38/0.61  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.61  thf('66', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.61  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['66'])).
% 0.38/0.61  thf('68', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['35', '40'])).
% 0.38/0.61  thf('69', plain,
% 0.38/0.61      (![X21 : $i, X23 : $i]:
% 0.38/0.61         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.61  thf('71', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         (((X15) != (k1_xboole_0))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ X15) = (X16))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      (![X16 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.38/0.61          | ((k8_setfam_1 @ X16 @ k1_xboole_0) = (X16)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['71'])).
% 0.38/0.61  thf('73', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.61          | ((k8_setfam_1 @ X0 @ k1_xboole_0) = (X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['70', '72'])).
% 0.38/0.61  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.61  thf('75', plain, (![X0 : $i]: ((k8_setfam_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.61  thf('76', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_k8_setfam_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.61  thf('77', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k8_setfam_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.38/0.61  thf('78', plain,
% 0.38/0.61      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.38/0.61  thf('79', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('80', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.38/0.61      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.61  thf('81', plain, ($false),
% 0.38/0.61      inference('demod', [status(thm)], ['0', '67', '75', '80'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
