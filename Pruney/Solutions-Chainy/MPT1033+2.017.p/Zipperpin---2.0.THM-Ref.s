%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L3byRh4wpK

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:06 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 284 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  706 (5443 expanded)
%              Number of equality atoms :   40 ( 262 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X23 = X20 )
      | ~ ( r1_partfun1 @ X23 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_partfun1 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
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
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
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
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_B_1 = sk_C_1 )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( sk_B_1 = sk_C_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('46',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_B_1 = sk_D )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1 = sk_D )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_C_1 = sk_D )
    | ( sk_C_1 = sk_D ) ),
    inference('sup+',[status(thm)],['39','47'])).

thf('49',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X19 @ X16 )
      | ( ( k1_funct_1 @ X19 @ ( sk_E @ X16 @ X19 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_E @ X16 @ X19 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t113_funct_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L3byRh4wpK
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:19:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 266 iterations in 0.156s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.41/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(t142_funct_2, conjecture,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ![D:$i]:
% 0.41/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60           ( ( r1_partfun1 @ C @ D ) =>
% 0.41/0.60             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.60               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60          ( ![D:$i]:
% 0.41/0.60            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60              ( ( r1_partfun1 @ C @ D ) =>
% 0.41/0.60                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.60                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.41/0.60  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc5_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.41/0.60             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.41/0.60          | (v1_partfun1 @ X13 @ X14)
% 0.41/0.60          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.41/0.60          | ~ (v1_funct_1 @ X13)
% 0.41/0.60          | (v1_xboole_0 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.41/0.60        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t148_partfun1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ![D:$i]:
% 0.41/0.60         ( ( ( v1_funct_1 @ D ) & 
% 0.41/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.41/0.60               ( r1_partfun1 @ C @ D ) ) =>
% 0.41/0.60             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (v1_funct_1 @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.60          | ((X23) = (X20))
% 0.41/0.60          | ~ (r1_partfun1 @ X23 @ X20)
% 0.41/0.60          | ~ (v1_partfun1 @ X20 @ X21)
% 0.41/0.60          | ~ (v1_partfun1 @ X23 @ X21)
% 0.41/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.60          | ~ (v1_funct_1 @ X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.41/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.41/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.41/0.60          | ((X0) = (sk_D))
% 0.41/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.60  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.41/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.41/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.41/0.60          | ((X0) = (sk_D)))),
% 0.41/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | ((X0) = (sk_D))
% 0.41/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.41/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.60          | ~ (v1_funct_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      ((~ (v1_funct_1 @ sk_C_1)
% 0.41/0.60        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.41/0.60        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.41/0.60        | ((sk_C_1) = (sk_D))
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '13'])).
% 0.41/0.60  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.41/0.60        | ((sk_C_1) = (sk_D))
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.41/0.60          | (v1_partfun1 @ X13 @ X14)
% 0.41/0.60          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.41/0.60          | ~ (v1_funct_1 @ X13)
% 0.41/0.60          | (v1_xboole_0 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_C_1)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.41/0.60        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('23', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.60  thf('24', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc4_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.60           ( v1_xboole_0 @ C ) ) ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X10)
% 0.41/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.41/0.60          | (v1_xboole_0 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.41/0.60  thf('27', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain, ((((sk_C_1) = (sk_D)) | (v1_xboole_0 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['24', '27'])).
% 0.41/0.60  thf('29', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.41/0.60  thf(d3_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i]:
% 0.41/0.60         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X7 : $i, X9 : $i]:
% 0.41/0.60         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((sk_C_1) = (sk_D)) | ~ (v1_xboole_0 @ X0) | ((sk_B_1) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((((sk_C_1) = (sk_D)) | ((sk_B_1) = (sk_C_1)) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['28', '37'])).
% 0.41/0.60  thf('39', plain, ((((sk_B_1) = (sk_C_1)) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('40', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X10)
% 0.41/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.41/0.60          | (v1_xboole_0 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.41/0.60  thf('43', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain, ((((sk_C_1) = (sk_D)) | (v1_xboole_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['40', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((sk_C_1) = (sk_D)) | ~ (v1_xboole_0 @ X0) | ((sk_B_1) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '36'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((((sk_C_1) = (sk_D)) | ((sk_B_1) = (sk_D)) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain, ((((sk_B_1) = (sk_D)) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      ((((sk_C_1) = (sk_D)) | ((sk_C_1) = (sk_D)) | ((sk_C_1) = (sk_D)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['39', '47'])).
% 0.41/0.60  thf('49', plain, (((sk_C_1) = (sk_D))),
% 0.41/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t113_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ![D:$i]:
% 0.41/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60           ( ( ![E:$i]:
% 0.41/0.60               ( ( m1_subset_1 @ E @ A ) =>
% 0.41/0.60                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.41/0.60             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (v1_funct_1 @ X16)
% 0.41/0.60          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.41/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.41/0.60          | (r2_relset_1 @ X17 @ X18 @ X19 @ X16)
% 0.41/0.60          | ((k1_funct_1 @ X19 @ (sk_E @ X16 @ X19 @ X17))
% 0.41/0.60              != (k1_funct_1 @ X16 @ (sk_E @ X16 @ X19 @ X17)))
% 0.41/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.41/0.60          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.41/0.60          | ~ (v1_funct_1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [t113_funct_2])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (v1_funct_1 @ X0)
% 0.41/0.60          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.60          | (r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.60          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.41/0.60          | ~ (v1_funct_1 @ X0))),
% 0.41/0.60      inference('eq_res', [status(thm)], ['51'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.60          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.41/0.60          | ~ (v1_funct_1 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      ((~ (v1_funct_1 @ sk_C_1)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.41/0.60        | (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '53'])).
% 0.41/0.60  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('56', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('57', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.60  thf('58', plain, ($false),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '49', '57'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
