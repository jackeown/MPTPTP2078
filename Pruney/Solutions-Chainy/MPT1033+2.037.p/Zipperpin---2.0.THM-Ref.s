%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GKgCMX5LqU

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:09 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 206 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   20
%              Number of atoms          :  855 (2610 expanded)
%              Number of equality atoms :   66 ( 174 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X24 = X21 )
      | ~ ( r1_partfun1 @ X24 @ X21 )
      | ~ ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_partfun1 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A_1 )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A_1 )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('32',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('33',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['31','36'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( r2_hidden @ ( sk_B @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('64',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('68',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D ) @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['49','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('89',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('91',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['37','91'])).

thf('93',plain,(
    sk_C_1 = sk_D ),
    inference(clc,[status(thm)],['24','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('96',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GKgCMX5LqU
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 386 iterations in 0.161s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.61  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.39/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.61  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.61  thf(t142_funct_2, conjecture,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.61       ( ![D:$i]:
% 0.39/0.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.61           ( ( r1_partfun1 @ C @ D ) =>
% 0.39/0.61             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.61               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.61          ( ![D:$i]:
% 0.39/0.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.61              ( ( r1_partfun1 @ C @ D ) =>
% 0.39/0.61                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.61                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.39/0.61  thf('0', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(cc5_funct_2, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.61       ( ![C:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.39/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.39/0.61          | (v1_partfun1 @ X18 @ X19)
% 0.39/0.61          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.39/0.61          | ~ (v1_funct_1 @ X18)
% 0.39/0.61          | (v1_xboole_0 @ X20))),
% 0.39/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.39/0.61        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.61        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1)
% 0.39/0.61        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t148_partfun1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.61       ( ![D:$i]:
% 0.39/0.61         ( ( ( v1_funct_1 @ D ) & 
% 0.39/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.61           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.39/0.61               ( r1_partfun1 @ C @ D ) ) =>
% 0.39/0.61             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.61         (~ (v1_funct_1 @ X21)
% 0.39/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.39/0.61          | ((X24) = (X21))
% 0.39/0.61          | ~ (r1_partfun1 @ X24 @ X21)
% 0.39/0.61          | ~ (v1_partfun1 @ X21 @ X22)
% 0.39/0.61          | ~ (v1_partfun1 @ X24 @ X22)
% 0.39/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.39/0.61          | ~ (v1_funct_1 @ X24))),
% 0.39/0.61      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (v1_funct_1 @ X0)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ 
% 0.39/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))
% 0.39/0.61          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.39/0.61          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.39/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.39/0.61          | ((X0) = (sk_D))
% 0.39/0.61          | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.61  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (v1_funct_1 @ X0)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ 
% 0.39/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))
% 0.39/0.61          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.39/0.61          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.39/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.39/0.61          | ((X0) = (sk_D)))),
% 0.39/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.39/0.61          | ((X0) = (sk_D))
% 0.39/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.39/0.61          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ 
% 0.39/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))
% 0.39/0.61          | ~ (v1_funct_1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['7', '12'])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      ((~ (v1_funct_1 @ sk_C_1)
% 0.39/0.61        | ~ (v1_partfun1 @ sk_C_1 @ sk_A_1)
% 0.39/0.61        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.39/0.61        | ((sk_C_1) = (sk_D))
% 0.39/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '13'])).
% 0.39/0.61  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      ((~ (v1_partfun1 @ sk_C_1 @ sk_A_1)
% 0.39/0.61        | ((sk_C_1) = (sk_D))
% 0.39/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.39/0.61          | (v1_partfun1 @ X18 @ X19)
% 0.39/0.61          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.39/0.61          | ~ (v1_funct_1 @ X18)
% 0.39/0.61          | (v1_xboole_0 @ X20))),
% 0.39/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.39/0.61        | ~ (v1_funct_1 @ sk_C_1)
% 0.39/0.61        | ~ (v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B_1)
% 0.39/0.61        | (v1_partfun1 @ sk_C_1 @ sk_A_1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.61  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C_1 @ sk_A_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.61  thf('24', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D)))),
% 0.39/0.61      inference('clc', [status(thm)], ['17', '23'])).
% 0.39/0.61  thf(l13_xboole_0, axiom,
% 0.39/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.39/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.39/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      ((((sk_B_1) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('split', [status(esa)], ['28'])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      ((![X0 : $i]:
% 0.39/0.61          (((X0) != (k1_xboole_0))
% 0.39/0.61           | ~ (v1_xboole_0 @ X0)
% 0.39/0.61           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.39/0.61         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.39/0.61         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.39/0.61  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.39/0.61  thf('32', plain, ((v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.39/0.61  thf('33', plain, ((v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.39/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.61  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.61  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('simplify_reflect+', [status(thm)], ['31', '36'])).
% 0.39/0.61  thf(d1_xboole_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.61  thf(t113_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['39'])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('split', [status(esa)], ['28'])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (((m1_subset_1 @ sk_D @ 
% 0.39/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.39/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['41', '42'])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.61         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['40', '43'])).
% 0.39/0.62  thf(t3_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf(d3_tarski, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.62          | (r2_hidden @ X3 @ X5)
% 0.39/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      ((![X0 : $i]:
% 0.39/0.62          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      ((((v1_xboole_0 @ sk_D) | (r2_hidden @ (sk_B @ sk_D) @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['38', '48'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X4 : $i, X6 : $i]:
% 0.39/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X4 : $i, X6 : $i]:
% 0.39/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.62  thf('54', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (![X11 : $i, X13 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('56', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.39/0.62  thf(reflexivity_r2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.39/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.39/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.39/0.62      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.39/0.62      inference('condensation', [status(thm)], ['58'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.62          | (r2_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['57', '59'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (![X0 : $i]: (r2_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['56', '60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r2_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0)
% 0.39/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['50', '61'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['28'])).
% 0.39/0.62  thf('64', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['28'])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['67', '70'])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.62          | (r2_hidden @ X3 @ X5)
% 0.39/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      ((![X0 : $i]:
% 0.39/0.62          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      ((((v1_xboole_0 @ sk_C_1) | (r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['66', '75'])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      ((((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.39/0.62  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('demod', [status(thm)], ['32', '35'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_C_1)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['65', '82'])).
% 0.39/0.62  thf('84', plain,
% 0.39/0.62      ((~ (v1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['62', '83'])).
% 0.39/0.62  thf('85', plain,
% 0.39/0.62      (((r2_hidden @ (sk_B @ sk_D) @ k1_xboole_0))
% 0.39/0.62         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('clc', [status(thm)], ['49', '84'])).
% 0.39/0.62  thf('86', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.62  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('demod', [status(thm)], ['32', '35'])).
% 0.39/0.62  thf('89', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['87', '88'])).
% 0.39/0.62  thf('90', plain,
% 0.39/0.62      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.39/0.62      inference('split', [status(esa)], ['28'])).
% 0.39/0.62  thf('91', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.62      inference('sat_resolution*', [status(thm)], ['89', '90'])).
% 0.39/0.62  thf('92', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['37', '91'])).
% 0.39/0.62  thf('93', plain, (((sk_C_1) = (sk_D))),
% 0.39/0.62      inference('clc', [status(thm)], ['24', '92'])).
% 0.39/0.62  thf('94', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('95', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.39/0.62      inference('condensation', [status(thm)], ['58'])).
% 0.39/0.62  thf('96', plain, ((r2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 0.39/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.62  thf('97', plain, ($false),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '93', '96'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
