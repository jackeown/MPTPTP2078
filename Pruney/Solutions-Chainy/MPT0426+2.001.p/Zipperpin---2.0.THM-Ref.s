%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y71ljJrrIa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:18 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 253 expanded)
%              Number of leaves         :   27 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  642 (2683 expanded)
%              Number of equality atoms :   36 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t58_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r2_hidden @ B @ A )
       => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
             => ( r2_hidden @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ C )
               => ( r2_hidden @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_setfam_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k6_setfam_1 @ X18 @ X17 )
        = ( k1_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('7',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_3 )
    = ( k1_setfam_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_3 )
      = ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_C_3 )
      | ( r2_hidden @ sk_B_1 @ X26 )
      | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_3 ) @ sk_D )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_D )
        | ~ ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_3 ) ) )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C_3 = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ sk_D ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
      & ( r2_hidden @ sk_D @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_C_3 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
      & ( r2_hidden @ sk_D @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_C_3 )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
      & ( r2_hidden @ sk_D @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X9: $i] :
      ( v1_xboole_0 @ ( sk_B @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_D @ sk_C_3 )
    | ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X25 @ X24 ) @ X24 )
      | ( r1_tarski @ X25 @ ( k1_setfam_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('36',plain,
    ( ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X26 ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X26 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('37',plain,
    ( ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X26 ) )
    | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('38',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_C_3 )
      | ( r2_hidden @ sk_B_1 @ X26 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32','37'])).

thf('39',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_C_3 )
      | ( r2_hidden @ sk_B_1 @ X26 ) ) ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( sk_C_2 @ X0 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('41',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_C_3 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( sk_C_2 @ X0 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( sk_C_2 @ X25 @ X24 ) )
      | ( r1_tarski @ X25 @ ( k1_setfam_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('47',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_3 )
      = ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('49',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_3 )
    = ( k1_setfam_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('50',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_3 )
      = ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','32'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','54'])).

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

thf('58',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( k8_setfam_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['34','55','59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y71ljJrrIa
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 323 iterations in 0.169s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.47/0.65  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.47/0.65  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.65  thf(t58_setfam_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.65       ( ( r2_hidden @ B @ A ) =>
% 0.47/0.65         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.47/0.65           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.65        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.65          ( ( r2_hidden @ B @ A ) =>
% 0.47/0.65            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.47/0.65              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      ((~ (r2_hidden @ sk_B_1 @ sk_D)
% 0.47/0.65        | ~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))
% 0.47/0.65         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) | 
% 0.47/0.65       ~ ((r2_hidden @ sk_B_1 @ sk_D))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (((r2_hidden @ sk_D @ sk_C_3)
% 0.47/0.65        | ~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (((r2_hidden @ sk_D @ sk_C_3)) | 
% 0.47/0.65       ~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k6_setfam_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.65       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         (((k6_setfam_1 @ X18 @ X17) = (k1_setfam_1 @ X17))
% 0.47/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.47/0.65  thf('7', plain, (((k6_setfam_1 @ sk_A @ sk_C_3) = (k1_setfam_1 @ sk_C_3))),
% 0.47/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d10_setfam_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.65       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.65           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.47/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (![X15 : $i, X16 : $i]:
% 0.47/0.65         (((X15) = (k1_xboole_0))
% 0.47/0.65          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.47/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.47/0.65      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      ((((k8_setfam_1 @ sk_A @ sk_C_3) = (k6_setfam_1 @ sk_A @ sk_C_3))
% 0.47/0.65        | ((sk_C_3) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X26 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X26 @ sk_C_3)
% 0.47/0.65          | (r2_hidden @ sk_B_1 @ X26)
% 0.47/0.65          | (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))
% 0.47/0.65         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 0.47/0.65      inference('split', [status(esa)], ['11'])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      ((((r2_hidden @ sk_B_1 @ (k6_setfam_1 @ sk_A @ sk_C_3))
% 0.47/0.65         | ((sk_C_3) = (k1_xboole_0))))
% 0.47/0.65         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 0.47/0.65      inference('sup+', [status(thm)], ['10', '12'])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      ((((r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.65         | ((sk_C_3) = (k1_xboole_0))))
% 0.47/0.65         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 0.47/0.65      inference('sup+', [status(thm)], ['7', '13'])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (((r2_hidden @ sk_D @ sk_C_3)) <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf(t4_setfam_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X19 : $i, X20 : $i]:
% 0.47/0.65         ((r1_tarski @ (k1_setfam_1 @ X19) @ X20) | ~ (r2_hidden @ X20 @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (((r1_tarski @ (k1_setfam_1 @ sk_C_3) @ sk_D))
% 0.47/0.65         <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.65  thf(d3_tarski, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.65          | (r2_hidden @ X0 @ X2)
% 0.47/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          ((r2_hidden @ X0 @ sk_D)
% 0.47/0.65           | ~ (r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_3))))
% 0.47/0.65         <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (((((sk_C_3) = (k1_xboole_0)) | (r2_hidden @ sk_B_1 @ sk_D)))
% 0.47/0.65         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) & 
% 0.47/0.65             ((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      ((~ (r2_hidden @ sk_B_1 @ sk_D)) <= (~ ((r2_hidden @ sk_B_1 @ sk_D)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      ((((sk_C_3) = (k1_xboole_0)))
% 0.47/0.65         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 0.47/0.65             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) & 
% 0.47/0.65             ((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (((r2_hidden @ sk_D @ sk_C_3)) <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf(t7_boole, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [t7_boole])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      ((~ (v1_xboole_0 @ sk_C_3)) <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 0.47/0.66             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) & 
% 0.47/0.66             ((r2_hidden @ sk_D @ sk_C_3)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '25'])).
% 0.47/0.66  thf(rc2_subset_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ?[B:$i]:
% 0.47/0.66       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.47/0.66  thf('27', plain, (![X9 : $i]: (v1_xboole_0 @ (sk_B @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.47/0.66  thf(t4_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.66  thf(cc1_subset_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X13 : $i, X14 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.47/0.66          | (v1_xboole_0 @ X13)
% 0.47/0.66          | ~ (v1_xboole_0 @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) | 
% 0.47/0.66       ~ ((r2_hidden @ sk_D @ sk_C_3)) | ((r2_hidden @ sk_B_1 @ sk_D))),
% 0.47/0.66      inference('demod', [status(thm)], ['26', '31'])).
% 0.47/0.66  thf('33', plain, (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['2', '4', '32'])).
% 0.47/0.66  thf('34', plain, (~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.47/0.66  thf(t6_setfam_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.47/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i]:
% 0.47/0.66         (((X24) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ (sk_C_2 @ X25 @ X24) @ X24)
% 0.47/0.66          | (r1_tarski @ X25 @ (k1_setfam_1 @ X24)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      ((![X26 : $i]:
% 0.47/0.66          (~ (r2_hidden @ X26 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X26)))
% 0.47/0.66         <= ((![X26 : $i]:
% 0.47/0.66                (~ (r2_hidden @ X26 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X26))))),
% 0.47/0.66      inference('split', [status(esa)], ['11'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      ((![X26 : $i]:
% 0.47/0.66          (~ (r2_hidden @ X26 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X26))) | 
% 0.47/0.66       ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.66      inference('split', [status(esa)], ['11'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      ((![X26 : $i]:
% 0.47/0.66          (~ (r2_hidden @ X26 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X26)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['2', '4', '32', '37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X26 : $i]: (~ (r2_hidden @ X26 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X26))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.66          | ((sk_C_3) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ sk_B_1 @ (sk_C_2 @ X0 @ sk_C_3)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['35', '39'])).
% 0.47/0.66  thf(l1_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X6 : $i, X8 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((sk_C_3) = (k1_xboole_0))
% 0.47/0.66          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.66          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (sk_C_2 @ X0 @ sk_C_3)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i]:
% 0.47/0.66         (((X24) = (k1_xboole_0))
% 0.47/0.66          | ~ (r1_tarski @ X25 @ (sk_C_2 @ X25 @ X24))
% 0.47/0.66          | (r1_tarski @ X25 @ (k1_setfam_1 @ X24)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.66        | ((sk_C_3) = (k1_xboole_0))
% 0.47/0.66        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.66        | ((sk_C_3) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      ((((sk_C_3) = (k1_xboole_0))
% 0.47/0.66        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_3)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i]:
% 0.47/0.66         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      ((((sk_C_3) = (k1_xboole_0))
% 0.47/0.66        | (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      ((((k8_setfam_1 @ sk_A @ sk_C_3) = (k6_setfam_1 @ sk_A @ sk_C_3))
% 0.47/0.66        | ((sk_C_3) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('49', plain, (((k6_setfam_1 @ sk_A @ sk_C_3) = (k1_setfam_1 @ sk_C_3))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      ((((k8_setfam_1 @ sk_A @ sk_C_3) = (k1_setfam_1 @ sk_C_3))
% 0.47/0.66        | ((sk_C_3) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (((~ (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.66         | ((sk_C_3) = (k1_xboole_0))))
% 0.47/0.66         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.66  thf('53', plain, (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['2', '4', '32'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((~ (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3))
% 0.47/0.66        | ((sk_C_3) = (k1_xboole_0)))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.47/0.66  thf('55', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.47/0.66      inference('clc', [status(thm)], ['47', '54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X15 : $i, X16 : $i]:
% 0.47/0.66         (((X15) != (k1_xboole_0))
% 0.47/0.66          | ((k8_setfam_1 @ X16 @ X15) = (X16))
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X16 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.47/0.66          | ((k8_setfam_1 @ X16 @ k1_xboole_0) = (X16)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.66  thf('59', plain, (![X16 : $i]: ((k8_setfam_1 @ X16 @ k1_xboole_0) = (X16))),
% 0.47/0.66      inference('demod', [status(thm)], ['57', '58'])).
% 0.47/0.66  thf('60', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('61', plain, ($false),
% 0.47/0.66      inference('demod', [status(thm)], ['34', '55', '59', '60'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
