%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vVuE5fdSl3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:23 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 898 expanded)
%              Number of leaves         :   27 ( 265 expanded)
%              Depth                    :   22
%              Number of atoms          :  719 (8791 expanded)
%              Number of equality atoms :   77 ( 691 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X19 @ X18 )
        = ( k6_setfam_1 @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( ( k6_setfam_1 @ X23 @ X22 )
        = ( k1_setfam_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X19 @ X18 )
        = ( k6_setfam_1 @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( ( k6_setfam_1 @ X23 @ X22 )
        = ( k1_setfam_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_tarski @ ( k1_setfam_1 @ X28 ) @ ( k1_setfam_1 @ X27 ) ) ) ),
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

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_xboole_0])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C = sk_B )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','51'])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['22','52'])).

thf('54',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','59'])).

thf('61',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X19 @ X18 )
        = X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('66',plain,(
    ! [X19: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) )
      | ( ( k8_setfam_1 @ X19 @ k1_xboole_0 )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['60'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('71',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('74',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('75',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('78',plain,(
    m1_subset_1 @ ( k6_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('82',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('85',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['72','83','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vVuE5fdSl3
% 0.15/0.37  % Computer   : n005.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:40:03 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 247 iterations in 0.176s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(t59_setfam_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( ![C:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65           ( ( r1_tarski @ B @ C ) =>
% 0.45/0.65             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65          ( ![C:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65              ( ( r1_tarski @ B @ C ) =>
% 0.45/0.65                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d10_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.45/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (((X18) = (k1_xboole_0))
% 0.45/0.65          | ((k8_setfam_1 @ X19 @ X18) = (k6_setfam_1 @ X19 @ X18))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.45/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k6_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i]:
% 0.45/0.65         (((k6_setfam_1 @ X23 @ X22) = (k1_setfam_1 @ X22))
% 0.45/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.45/0.65  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.45/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (((X18) = (k1_xboole_0))
% 0.45/0.65          | ((k8_setfam_1 @ X19 @ X18) = (k6_setfam_1 @ X19 @ X18))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.45/0.65           (k6_setfam_1 @ sk_A @ sk_B))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i]:
% 0.45/0.65         (((k6_setfam_1 @ X23 @ X22) = (k1_setfam_1 @ X22))
% 0.45/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.45/0.65  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.45/0.65        | ((sk_C) = (k1_xboole_0))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '16'])).
% 0.45/0.65  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t7_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) =>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i]:
% 0.45/0.65         (((X27) = (k1_xboole_0))
% 0.45/0.65          | ~ (r1_tarski @ X27 @ X28)
% 0.45/0.65          | (r1_tarski @ (k1_setfam_1 @ X28) @ (k1_setfam_1 @ X27)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.65      inference('clc', [status(thm)], ['17', '20'])).
% 0.45/0.65  thf('22', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.65      inference('clc', [status(thm)], ['17', '20'])).
% 0.45/0.65  thf(t6_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf(t37_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X7 : $i, X9 : $i]:
% 0.45/0.65         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.45/0.65  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X1) = (k4_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf(t83_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X13 : $i, X15 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.65  thf('34', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['30', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i]:
% 0.45/0.65         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.65          | (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['29', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['23', '41'])).
% 0.45/0.65  thf('43', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i]:
% 0.45/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('45', plain, ((~ (r1_tarski @ sk_C @ sk_B) | ((sk_C) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_C) | ((sk_C) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['42', '45'])).
% 0.45/0.65  thf('47', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t12_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i]:
% 0.45/0.65         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.65  thf('49', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.65  thf(fc4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.65       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ A @ B ) ) ) ))).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc4_xboole_0])).
% 0.45/0.65  thf('51', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf('52', plain, ((((sk_C) = (sk_B)) | ~ (v1_xboole_0 @ sk_C))),
% 0.45/0.65      inference('clc', [status(thm)], ['46', '51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.65        | ((sk_B) = (k1_xboole_0))
% 0.45/0.65        | ((sk_C) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '52'])).
% 0.45/0.65  thf('54', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.65  thf(t69_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.65       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X10 @ X11)
% 0.45/0.65          | ~ (r1_tarski @ X10 @ X11)
% 0.45/0.65          | (v1_xboole_0 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('59', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['53', '58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      ((((k1_xboole_0) = (sk_B))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0))
% 0.45/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['21', '59'])).
% 0.45/0.65  thf('61', plain, (((k1_xboole_0) = (sk_B))),
% 0.45/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.45/0.65          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['0', '61'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i]:
% 0.45/0.65         (((X18) != (k1_xboole_0))
% 0.45/0.65          | ((k8_setfam_1 @ X19 @ X18) = (X19))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19)))
% 0.45/0.65          | ((k8_setfam_1 @ X19 @ k1_xboole_0) = (X19)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.45/0.65          | ~ (v1_xboole_0 @ X0)
% 0.45/0.65          | ((k8_setfam_1 @ X1 @ k1_xboole_0) = (X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A)) | ~ (v1_xboole_0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '67'])).
% 0.45/0.65  thf('69', plain, (((k1_xboole_0) = (sk_B))),
% 0.45/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.45/0.65  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('71', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.45/0.65  thf('72', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['62', '71'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.45/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.65  thf('74', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['62', '71'])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ sk_A) | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_k6_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.65       ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (k6_setfam_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))
% 0.45/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_setfam_1])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      ((m1_subset_1 @ (k6_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.65  thf(t3_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.65  thf('80', plain, ((r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('81', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('82', plain, ((r1_tarski @ (k1_setfam_1 @ sk_C) @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.65  thf('83', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['75', '82'])).
% 0.45/0.65  thf('84', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.45/0.65  thf('85', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf('86', plain, ($false),
% 0.45/0.65      inference('demod', [status(thm)], ['72', '83', '84', '85'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
