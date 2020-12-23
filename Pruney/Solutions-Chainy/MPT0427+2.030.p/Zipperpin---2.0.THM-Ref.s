%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RFzaBKWE4k

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:24 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 173 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  653 (1529 expanded)
%              Number of equality atoms :   45 (  80 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_tarski @ ( k1_setfam_1 @ X24 ) @ ( k1_setfam_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = ( k6_setfam_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k6_setfam_1 @ sk_A @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_2 )
    = ( k1_setfam_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k1_setfam_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = ( k6_setfam_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_setfam_1 @ X19 @ X18 )
        = ( k1_setfam_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X15 @ X14 )
        = X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('25',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
        = X15 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X12: $i] :
      ( ( r1_xboole_0 @ X12 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('27',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('30',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i] :
      ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_setfam_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','46'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['47','54'])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','55'])).

thf('57',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','64'])).

thf('66',plain,(
    ! [X15: $i] :
      ( ( k8_setfam_1 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(demod,[status(thm)],['25','36'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('69',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65','66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RFzaBKWE4k
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:57:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 231 iterations in 0.117s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.40/0.57  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.40/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.57  thf(t59_setfam_1, conjecture,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57       ( ![C:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57           ( ( r1_tarski @ B @ C ) =>
% 0.40/0.57             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i]:
% 0.40/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57          ( ![C:$i]:
% 0.40/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57              ( ( r1_tarski @ B @ C ) =>
% 0.40/0.57                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.40/0.57          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('1', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t7_setfam_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.40/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.57         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X23 : $i, X24 : $i]:
% 0.40/0.57         (((X23) = (k1_xboole_0))
% 0.40/0.57          | ~ (r1_tarski @ X23 @ X24)
% 0.40/0.57          | (r1_tarski @ (k1_setfam_1 @ X24) @ (k1_setfam_1 @ X23)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (((r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.40/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d10_setfam_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.57           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.40/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      (![X14 : $i, X15 : $i]:
% 0.40/0.57         (((X14) = (k1_xboole_0))
% 0.40/0.57          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.40/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k6_setfam_1 @ sk_A @ sk_C_2))
% 0.40/0.57        | ((sk_C_2) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(redefinition_k6_setfam_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X18 : $i, X19 : $i]:
% 0.40/0.57         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.40/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.40/0.57  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))
% 0.40/0.57        | ((sk_C_2) = (k1_xboole_0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['6', '9'])).
% 0.40/0.57  thf('11', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X14 : $i, X15 : $i]:
% 0.40/0.57         (((X14) = (k1_xboole_0))
% 0.40/0.57          | ((k8_setfam_1 @ X15 @ X14) = (k6_setfam_1 @ X15 @ X14))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.40/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.40/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.40/0.57          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.40/0.57           (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.40/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X18 : $i, X19 : $i]:
% 0.40/0.57         (((k6_setfam_1 @ X19 @ X18) = (k1_setfam_1 @ X18))
% 0.40/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.40/0.57  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.40/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.40/0.57        | ((sk_C_2) = (k1_xboole_0))
% 0.40/0.57        | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['10', '19'])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      ((((sk_B_1) = (k1_xboole_0))
% 0.40/0.57        | ((sk_B_1) = (k1_xboole_0))
% 0.40/0.57        | ((sk_C_2) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['3', '20'])).
% 0.40/0.57  thf('22', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.57  thf(l13_xboole_0, axiom,
% 0.40/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.40/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X14 : $i, X15 : $i]:
% 0.40/0.57         (((X14) != (k1_xboole_0))
% 0.40/0.57          | ((k8_setfam_1 @ X15 @ X14) = (X15))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.40/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X15 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.40/0.57          | ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.57  thf(t66_xboole_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.40/0.57       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X12 : $i]: ((r1_xboole_0 @ X12 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.40/0.57  thf('27', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.57  thf(d3_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X4 : $i, X6 : $i]:
% 0.40/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X4 : $i, X6 : $i]:
% 0.40/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf(t3_xboole_0, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X10 @ X8)
% 0.40/0.57          | ~ (r2_hidden @ X10 @ X11)
% 0.40/0.57          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_tarski @ X0 @ X1)
% 0.40/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.57          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('32', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ X0 @ X1)
% 0.40/0.57          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.40/0.57          | (r1_tarski @ X0 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['28', '31'])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.40/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.40/0.57  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.57      inference('sup-', [status(thm)], ['27', '33'])).
% 0.40/0.57  thf(t3_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.57  thf('35', plain,
% 0.40/0.57      (![X20 : $i, X22 : $i]:
% 0.40/0.57         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('36', plain,
% 0.40/0.57      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.57  thf('37', plain, (![X15 : $i]: ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15))),
% 0.40/0.57      inference('demod', [status(thm)], ['25', '36'])).
% 0.40/0.57  thf('38', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['23', '37'])).
% 0.40/0.57  thf('39', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((k8_setfam_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['23', '37'])).
% 0.40/0.57  thf('40', plain,
% 0.40/0.57      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.40/0.57          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ sk_A)
% 0.40/0.57        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.57  thf('42', plain,
% 0.40/0.57      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.40/0.57        | ~ (v1_xboole_0 @ sk_C_2)
% 0.40/0.57        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['38', '41'])).
% 0.40/0.57  thf('43', plain,
% 0.40/0.57      (![X4 : $i, X6 : $i]:
% 0.40/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('44', plain,
% 0.40/0.57      (![X4 : $i, X6 : $i]:
% 0.40/0.57         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('45', plain,
% 0.40/0.57      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.57  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.40/0.57  thf('47', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.40/0.57      inference('demod', [status(thm)], ['42', '46'])).
% 0.40/0.57  thf(d1_xboole_0, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.57  thf('48', plain,
% 0.40/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.57  thf('49', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('50', plain,
% 0.40/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X3 @ X4)
% 0.40/0.57          | (r2_hidden @ X3 @ X5)
% 0.40/0.57          | ~ (r1_tarski @ X4 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('51', plain,
% 0.40/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.57  thf('52', plain,
% 0.40/0.57      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['48', '51'])).
% 0.40/0.57  thf('53', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.57  thf('54', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C_2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.40/0.57  thf('55', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.40/0.57      inference('clc', [status(thm)], ['47', '54'])).
% 0.40/0.57  thf('56', plain,
% 0.40/0.57      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['22', '55'])).
% 0.40/0.57  thf('57', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.57  thf('58', plain,
% 0.40/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.57  thf('59', plain,
% 0.40/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.57  thf('60', plain,
% 0.40/0.57      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X10 @ X8)
% 0.40/0.57          | ~ (r2_hidden @ X10 @ X11)
% 0.40/0.57          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('61', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ X0)
% 0.40/0.57          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.40/0.57          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.57  thf('62', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['58', '61'])).
% 0.40/0.57  thf('63', plain,
% 0.40/0.57      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['62'])).
% 0.40/0.57  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.57      inference('sup-', [status(thm)], ['57', '63'])).
% 0.40/0.57  thf('65', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['56', '64'])).
% 0.40/0.57  thf('66', plain, (![X15 : $i]: ((k8_setfam_1 @ X15 @ k1_xboole_0) = (X15))),
% 0.40/0.57      inference('demod', [status(thm)], ['25', '36'])).
% 0.40/0.57  thf('67', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(dt_k8_setfam_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.57       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.57  thf('68', plain,
% 0.40/0.57      (![X16 : $i, X17 : $i]:
% 0.40/0.57         ((m1_subset_1 @ (k8_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.40/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.40/0.57  thf('69', plain,
% 0.40/0.57      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.40/0.57  thf('70', plain,
% 0.40/0.57      (![X20 : $i, X21 : $i]:
% 0.40/0.57         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('71', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ sk_A)),
% 0.40/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.40/0.57  thf('72', plain, ($false),
% 0.40/0.57      inference('demod', [status(thm)], ['0', '65', '66', '71'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
