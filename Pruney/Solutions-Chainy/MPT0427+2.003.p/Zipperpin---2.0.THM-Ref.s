%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noAxsx0MtI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:20 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 323 expanded)
%              Number of leaves         :   23 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  652 (3244 expanded)
%              Number of equality atoms :   59 ( 203 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = ( k6_setfam_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = ( k6_setfam_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('15',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

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
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ ( k1_setfam_1 @ X20 ) @ ( k1_setfam_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C = sk_B )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['22','48'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( ( r1_xboole_0 @ X4 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('51',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','56'])).

thf('58',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X11 @ X10 )
        = X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('63',plain,(
    ! [X11: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( ( k8_setfam_1 @ X11 @ k1_xboole_0 )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['57'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('68',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('71',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['59','68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noAxsx0MtI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 191 iterations in 0.104s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.36/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(t59_setfam_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56       ( ![C:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56           ( ( r1_tarski @ B @ C ) =>
% 0.36/0.56             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i]:
% 0.36/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56          ( ![C:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56              ( ( r1_tarski @ B @ C ) =>
% 0.36/0.56                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(d10_setfam_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.56           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.36/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i]:
% 0.36/0.56         (((X10) = (k1_xboole_0))
% 0.36/0.56          | ((k8_setfam_1 @ X11 @ X10) = (k6_setfam_1 @ X11 @ X10))
% 0.36/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.36/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k6_setfam_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i]:
% 0.36/0.56         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.36/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.36/0.56  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['3', '6'])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i]:
% 0.36/0.56         (((X10) = (k1_xboole_0))
% 0.36/0.56          | ((k8_setfam_1 @ X11 @ X10) = (k6_setfam_1 @ X11 @ X10))
% 0.36/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.36/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.36/0.56           (k6_setfam_1 @ sk_A @ sk_B))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i]:
% 0.36/0.56         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.36/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.36/0.56  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['12', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '16'])).
% 0.36/0.56  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t7_setfam_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.56         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i]:
% 0.36/0.56         (((X19) = (k1_xboole_0))
% 0.36/0.56          | ~ (r1_tarski @ X19 @ X20)
% 0.36/0.56          | (r1_tarski @ (k1_setfam_1 @ X20) @ (k1_setfam_1 @ X19)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.56  thf('21', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('clc', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf('22', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('clc', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf(l13_xboole_0, axiom,
% 0.36/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.56  thf(d10_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.36/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.56  thf('25', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.36/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.56  thf(t3_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X16 : $i, X18 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('27', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.56  thf(dt_k8_setfam_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.56       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X12 : $i, X13 : $i]:
% 0.36/0.56         ((m1_subset_1 @ (k8_setfam_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.36/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (m1_subset_1 @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ 
% 0.36/0.56          (k1_zfmisc_1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.56  thf(cc1_subset_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X8 : $i, X9 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.36/0.56          | (v1_xboole_0 @ X8)
% 0.36/0.56          | ~ (v1_xboole_0 @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ X0)
% 0.36/0.56          | (v1_xboole_0 @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ X0)
% 0.36/0.56          | ((k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (m1_subset_1 @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ 
% 0.36/0.56          (k1_zfmisc_1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i]:
% 0.36/0.56         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X0 : $i]: (r1_tarski @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.36/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['33', '36'])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.56      inference('sup+', [status(thm)], ['23', '37'])).
% 0.36/0.56  thf('39', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.56  thf('41', plain, ((~ (r1_tarski @ sk_C @ sk_B) | ((sk_C) = (sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_C) | ((sk_C) = (sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['38', '41'])).
% 0.36/0.56  thf('43', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (![X16 : $i, X18 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      (![X8 : $i, X9 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.36/0.56          | (v1_xboole_0 @ X8)
% 0.36/0.56          | ~ (v1_xboole_0 @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.56  thf('47', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.56  thf('48', plain, ((((sk_C) = (sk_B)) | ~ (v1_xboole_0 @ sk_C))),
% 0.36/0.56      inference('clc', [status(thm)], ['42', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_C) = (sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '48'])).
% 0.36/0.56  thf(t66_xboole_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.36/0.56       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (![X4 : $i]: ((r1_xboole_0 @ X4 @ X4) | ((X4) != (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.36/0.56  thf('51', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.56  thf(t69_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i]:
% 0.36/0.56         (~ (r1_xboole_0 @ X6 @ X7)
% 0.36/0.56          | ~ (r1_tarski @ X6 @ X7)
% 0.36/0.56          | (v1_xboole_0 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.56  thf('54', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.36/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.56  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.56  thf('56', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['49', '55'])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      ((((k1_xboole_0) = (sk_B))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['21', '56'])).
% 0.36/0.56  thf('58', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.56      inference('simplify', [status(thm)], ['57'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.36/0.56          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['0', '58'])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i]:
% 0.36/0.56         (((X10) != (k1_xboole_0))
% 0.36/0.56          | ((k8_setfam_1 @ X11 @ X10) = (X11))
% 0.36/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.36/0.56      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (![X11 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.36/0.56          | ((k8_setfam_1 @ X11 @ k1_xboole_0) = (X11)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.36/0.56          | ~ (v1_xboole_0 @ X0)
% 0.36/0.56          | ((k8_setfam_1 @ X1 @ k1_xboole_0) = (X1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['61', '63'])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      ((((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A)) | ~ (v1_xboole_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['60', '64'])).
% 0.36/0.56  thf('66', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.56      inference('simplify', [status(thm)], ['57'])).
% 0.36/0.56  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.56  thf('68', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      (![X12 : $i, X13 : $i]:
% 0.36/0.56         ((m1_subset_1 @ (k8_setfam_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.36/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i]:
% 0.36/0.56         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('73', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.56  thf('74', plain, ($false),
% 0.36/0.56      inference('demod', [status(thm)], ['59', '68', '73'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
