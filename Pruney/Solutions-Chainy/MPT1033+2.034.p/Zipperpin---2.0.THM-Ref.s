%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLvXNlICNv

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:09 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 167 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  768 (2449 expanded)
%              Number of equality atoms :   62 ( 157 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X30 = X27 )
      | ~ ( r1_partfun1 @ X30 @ X27 )
      | ~ ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_partfun1 @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
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
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( sk_C = sk_D )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('41',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','56'])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('68',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','69'])).

thf('71',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('72',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','72'])).

thf('74',plain,(
    sk_C = sk_D ),
    inference('simplify_reflect-',[status(thm)],['33','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLvXNlICNv
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 270 iterations in 0.136s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.59  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.42/0.59  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(t142_funct_2, conjecture,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59       ( ![D:$i]:
% 0.42/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59           ( ( r1_partfun1 @ C @ D ) =>
% 0.42/0.59             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.42/0.59               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59          ( ![D:$i]:
% 0.42/0.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59              ( ( r1_partfun1 @ C @ D ) =>
% 0.42/0.59                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.42/0.59                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.42/0.59  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(cc5_funct_2, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.59       ( ![C:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.42/0.59             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.59          | (v1_partfun1 @ X24 @ X25)
% 0.42/0.59          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.42/0.59          | ~ (v1_funct_1 @ X24)
% 0.42/0.59          | (v1_xboole_0 @ X26))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (((v1_xboole_0 @ sk_B_2)
% 0.42/0.59        | ~ (v1_funct_1 @ sk_D)
% 0.42/0.59        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_2)
% 0.42/0.59        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.59  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('7', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t148_partfun1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59       ( ![D:$i]:
% 0.42/0.59         ( ( ( v1_funct_1 @ D ) & 
% 0.42/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.42/0.59               ( r1_partfun1 @ C @ D ) ) =>
% 0.42/0.59             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.42/0.59  thf('9', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.59         (~ (v1_funct_1 @ X27)
% 0.42/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.42/0.59          | ((X30) = (X27))
% 0.42/0.59          | ~ (r1_partfun1 @ X30 @ X27)
% 0.42/0.59          | ~ (v1_partfun1 @ X27 @ X28)
% 0.42/0.59          | ~ (v1_partfun1 @ X30 @ X28)
% 0.42/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.42/0.59          | ~ (v1_funct_1 @ X30))),
% 0.42/0.59      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (v1_funct_1 @ X0)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.42/0.59          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.42/0.59          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.42/0.59          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.42/0.59          | ((X0) = (sk_D))
% 0.42/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (v1_funct_1 @ X0)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.42/0.59          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.42/0.59          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.42/0.59          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.42/0.59          | ((X0) = (sk_D)))),
% 0.42/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v1_xboole_0 @ sk_B_2)
% 0.42/0.59          | ((X0) = (sk_D))
% 0.42/0.59          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.42/0.59          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.42/0.59          | ~ (v1_funct_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['7', '12'])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.42/0.59        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.42/0.59        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.42/0.59        | ((sk_C) = (sk_D))
% 0.42/0.59        | (v1_xboole_0 @ sk_B_2))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '13'])).
% 0.42/0.59  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.42/0.59        | ((sk_C) = (sk_D))
% 0.42/0.59        | (v1_xboole_0 @ sk_B_2))),
% 0.42/0.59      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.59          | (v1_partfun1 @ X24 @ X25)
% 0.42/0.59          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.42/0.59          | ~ (v1_funct_1 @ X24)
% 0.42/0.59          | (v1_xboole_0 @ X26))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      (((v1_xboole_0 @ sk_B_2)
% 0.42/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.42/0.59        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('23', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.42/0.59  thf('24', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_C) = (sk_D)))),
% 0.42/0.59      inference('clc', [status(thm)], ['17', '23'])).
% 0.42/0.59  thf(t9_mcart_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.59                 ( ![C:$i,D:$i]:
% 0.42/0.59                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.42/0.59                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      (![X21 : $i]:
% 0.42/0.59         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X21) @ X21))),
% 0.42/0.59      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.42/0.59  thf(d10_xboole_0, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.42/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.59  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.42/0.59  thf(t3_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (![X8 : $i, X10 : $i]:
% 0.42/0.59         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.59  thf(t5_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.42/0.59          ( v1_xboole_0 @ C ) ) ))).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X14 @ X15)
% 0.42/0.59          | ~ (v1_xboole_0 @ X16)
% 0.42/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['25', '31'])).
% 0.42/0.59  thf('33', plain, ((((sk_C) = (sk_D)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['24', '32'])).
% 0.42/0.59  thf('34', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['34'])).
% 0.42/0.59  thf(t4_subset_1, axiom,
% 0.42/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.42/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.59  thf(reflexivity_r2_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.42/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.59         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.42/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.42/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.42/0.59      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.42/0.59      inference('condensation', [status(thm)], ['37'])).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.59      inference('sup-', [status(thm)], ['36', '38'])).
% 0.42/0.59  thf('40', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['34'])).
% 0.42/0.59  thf('41', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.59  thf(t113_zfmisc_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      (![X4 : $i, X5 : $i]:
% 0.42/0.59         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.59  thf('44', plain,
% 0.42/0.59      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.42/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.42/0.59  thf('45', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['34'])).
% 0.42/0.59  thf('46', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('47', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_C @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.42/0.59  thf('48', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['44', '47'])).
% 0.42/0.59  thf('49', plain,
% 0.42/0.59      (![X8 : $i, X9 : $i]:
% 0.42/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('50', plain,
% 0.42/0.59      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.59  thf('51', plain,
% 0.42/0.59      (![X0 : $i, X2 : $i]:
% 0.42/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.59  thf('52', plain,
% 0.42/0.59      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.59  thf('53', plain,
% 0.42/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.42/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.59  thf('54', plain,
% 0.42/0.59      (![X8 : $i, X9 : $i]:
% 0.42/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.59  thf('56', plain,
% 0.42/0.59      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['52', '55'])).
% 0.42/0.59  thf('57', plain,
% 0.42/0.59      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['42', '56'])).
% 0.42/0.59  thf('58', plain,
% 0.42/0.59      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.42/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.42/0.59  thf('59', plain,
% 0.42/0.59      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('split', [status(esa)], ['34'])).
% 0.42/0.59  thf('60', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('61', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ 
% 0.42/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.42/0.59  thf('62', plain,
% 0.42/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup+', [status(thm)], ['58', '61'])).
% 0.42/0.59  thf('63', plain,
% 0.42/0.59      (![X8 : $i, X9 : $i]:
% 0.42/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('64', plain,
% 0.42/0.59      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.59  thf('65', plain,
% 0.42/0.59      (![X0 : $i, X2 : $i]:
% 0.42/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.59  thf('66', plain,
% 0.42/0.59      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.59  thf('67', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.59  thf('68', plain,
% 0.42/0.59      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['66', '67'])).
% 0.42/0.59  thf('69', plain,
% 0.42/0.59      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.42/0.59         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.59      inference('demod', [status(thm)], ['57', '68'])).
% 0.42/0.59  thf('70', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['39', '69'])).
% 0.42/0.59  thf('71', plain,
% 0.42/0.59      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.42/0.59      inference('split', [status(esa)], ['34'])).
% 0.42/0.59  thf('72', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.42/0.59      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.42/0.59  thf('73', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.42/0.59      inference('simpl_trail', [status(thm)], ['35', '72'])).
% 0.42/0.59  thf('74', plain, (((sk_C) = (sk_D))),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['33', '73'])).
% 0.42/0.59  thf('75', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('76', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.42/0.59      inference('condensation', [status(thm)], ['37'])).
% 0.42/0.59  thf('77', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C)),
% 0.42/0.59      inference('sup-', [status(thm)], ['75', '76'])).
% 0.42/0.59  thf('78', plain, ($false),
% 0.42/0.59      inference('demod', [status(thm)], ['0', '74', '77'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
