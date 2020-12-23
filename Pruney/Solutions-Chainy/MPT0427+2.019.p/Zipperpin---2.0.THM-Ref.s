%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xXGLbTY060

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 339 expanded)
%              Number of leaves         :   26 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          :  820 (3087 expanded)
%              Number of equality atoms :   56 ( 145 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = ( k6_setfam_1 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( ( k6_setfam_1 @ X22 @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
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
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_1 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X14 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i] :
      ( ( r1_xboole_0 @ X13 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('49',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['47','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','66'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','68'])).

thf('70',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('71',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X18 @ X17 )
        = X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('84',plain,(
    ! [X18: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( ( k8_setfam_1 @ X18 @ k1_xboole_0 )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['78'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','76'])).

thf('89',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('92',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['80','89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xXGLbTY060
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 212 iterations in 0.133s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.59  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.59  thf(t59_setfam_1, conjecture,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59       ( ![C:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.59             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i]:
% 0.20/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59          ( ![C:$i]:
% 0.20/0.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59              ( ( r1_tarski @ B @ C ) =>
% 0.20/0.59                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.59          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d10_setfam_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.59           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.20/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (((X17) = (k1_xboole_0))
% 0.20/0.59          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.20/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i]:
% 0.20/0.59         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.20/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.59  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.20/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (((X17) = (k1_xboole_0))
% 0.20/0.59          | ((k8_setfam_1 @ X18 @ X17) = (k6_setfam_1 @ X18 @ X17))
% 0.20/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i]:
% 0.20/0.59         (((k6_setfam_1 @ X22 @ X21) = (k1_setfam_1 @ X21))
% 0.20/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.59  thf('13', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.59          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.20/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '16'])).
% 0.20/0.59  thf('18', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t7_setfam_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.59         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X26 : $i, X27 : $i]:
% 0.20/0.59         (((X26) = (k1_xboole_0))
% 0.20/0.59          | ~ (r1_tarski @ X26 @ X27)
% 0.20/0.59          | (r1_tarski @ (k1_setfam_1 @ X27) @ (k1_setfam_1 @ X26)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (((r1_tarski @ (k1_setfam_1 @ sk_C_1) @ (k1_setfam_1 @ sk_B_1))
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.59  thf('21', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('clc', [status(thm)], ['17', '20'])).
% 0.20/0.59  thf('22', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t3_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf(d1_xboole_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.59  thf(t66_xboole_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.59       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      (![X14 : $i]: (((X14) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X14 @ X14))),
% 0.20/0.59      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.59  thf(d10_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.59  thf('28', plain,
% 0.20/0.59      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.59  thf('29', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.20/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.59  thf(t3_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (![X23 : $i, X25 : $i]:
% 0.20/0.59         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.59  thf(dt_k8_setfam_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (k8_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.20/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (m1_subset_1 @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ 
% 0.20/0.59          (k1_zfmisc_1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (![X23 : $i, X24 : $i]:
% 0.20/0.59         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (![X0 : $i]: (r1_tarski @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.59  thf(t69_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.59       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.59  thf('39', plain,
% 0.20/0.59      (![X15 : $i, X16 : $i]:
% 0.20/0.59         (~ (r1_xboole_0 @ X15 @ X16)
% 0.20/0.59          | ~ (r1_tarski @ X15 @ X16)
% 0.20/0.59          | (v1_xboole_0 @ X15))),
% 0.20/0.59      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.59  thf('40', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1) | ~ (r1_tarski @ X1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v1_xboole_0 @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['35', '40'])).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.59  thf('43', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v1_xboole_0 @ X0)
% 0.20/0.59          | ((k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      (![X0 : $i]: (r1_tarski @ (k8_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (![X7 : $i, X9 : $i]:
% 0.20/0.59         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v1_xboole_0 @ X0)
% 0.20/0.59          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.20/0.59          | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      (![X13 : $i]: ((r1_xboole_0 @ X13 @ X13) | ((X13) != (k1_xboole_0)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.59  thf('49', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.59          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.59          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.20/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.59  thf('54', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.59          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.59  thf('55', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.59  thf('56', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['49', '55'])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.59          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.59          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.59  thf('61', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.59          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.59          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['57', '60'])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.59  thf('63', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['56', '62'])).
% 0.20/0.59  thf('64', plain,
% 0.20/0.59      (![X15 : $i, X16 : $i]:
% 0.20/0.59         (~ (r1_xboole_0 @ X15 @ X16)
% 0.20/0.59          | ~ (r1_tarski @ X15 @ X16)
% 0.20/0.59          | (v1_xboole_0 @ X15))),
% 0.20/0.59      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.59  thf('65', plain,
% 0.20/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.59      inference('clc', [status(thm)], ['47', '65'])).
% 0.20/0.59  thf('67', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.59          | ~ (v1_xboole_0 @ X0)
% 0.20/0.59          | ((X1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['27', '66'])).
% 0.20/0.59  thf('68', plain, ((((sk_B_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['22', '67'])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['21', '68'])).
% 0.20/0.59  thf('70', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.59  thf('71', plain,
% 0.20/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.59  thf('72', plain,
% 0.20/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.59  thf('73', plain,
% 0.20/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.59          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('74', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((v1_xboole_0 @ X0)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.59          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.59  thf('75', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['71', '74'])).
% 0.20/0.59  thf('76', plain,
% 0.20/0.59      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.59  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['70', '76'])).
% 0.20/0.59  thf('78', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('demod', [status(thm)], ['69', '77'])).
% 0.20/0.59  thf('79', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.59  thf('80', plain,
% 0.20/0.59      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.59          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.20/0.59      inference('demod', [status(thm)], ['0', '79'])).
% 0.20/0.59  thf('81', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('82', plain,
% 0.20/0.59      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.59  thf('83', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (((X17) != (k1_xboole_0))
% 0.20/0.59          | ((k8_setfam_1 @ X18 @ X17) = (X18))
% 0.20/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.59  thf('84', plain,
% 0.20/0.59      (![X18 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.20/0.59          | ((k8_setfam_1 @ X18 @ k1_xboole_0) = (X18)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.59  thf('85', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.20/0.59          | ~ (v1_xboole_0 @ X0)
% 0.20/0.59          | ((k8_setfam_1 @ X1 @ k1_xboole_0) = (X1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['82', '84'])).
% 0.20/0.59  thf('86', plain,
% 0.20/0.59      ((((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))
% 0.20/0.59        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['81', '85'])).
% 0.20/0.59  thf('87', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.59  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['70', '76'])).
% 0.20/0.59  thf('89', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.20/0.59  thf('90', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('91', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (k8_setfam_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.20/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.20/0.59  thf('92', plain,
% 0.20/0.59      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.59  thf('93', plain,
% 0.20/0.59      (![X23 : $i, X24 : $i]:
% 0.20/0.59         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('94', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.59  thf('95', plain, ($false),
% 0.20/0.59      inference('demod', [status(thm)], ['80', '89', '94'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
