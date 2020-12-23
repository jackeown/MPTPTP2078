%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1039+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jeDNjTc3tt

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  162 (2421 expanded)
%              Number of leaves         :   29 ( 668 expanded)
%              Depth                    :   28
%              Number of atoms          : 1720 (53848 expanded)
%              Number of equality atoms :   74 (2781 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t154_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ~ ( ( ( B = k1_xboole_0 )
               => ( A = k1_xboole_0 ) )
              & ( r1_partfun1 @ C @ D )
              & ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ A @ B )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ~ ( ( r1_partfun1 @ C @ E )
                      & ( r1_partfun1 @ D @ E ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ~ ( ( ( B = k1_xboole_0 )
                 => ( A = k1_xboole_0 ) )
                & ( r1_partfun1 @ C @ D )
                & ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( v1_funct_2 @ E @ A @ B )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                   => ~ ( ( r1_partfun1 @ C @ E )
                        & ( r1_partfun1 @ D @ E ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
            & ( v1_funct_1 @ D ) )
         => ~ ( ! [E: $i] :
                  ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                    & ( v1_funct_1 @ E ) )
                 => ~ ( ( r1_partfun1 @ D @ E )
                      & ( r1_partfun1 @ C @ E )
                      & ( v1_partfun1 @ E @ A ) ) )
              & ( r1_partfun1 @ C @ D )
              & ( ( B = k1_xboole_0 )
               => ( A = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ E @ B @ A )
       => ~ ( zip_tseitin_1 @ E @ D @ C @ A ) )
     => ( zip_tseitin_2 @ E @ D @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_1 @ X10 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ C @ A )
     => ( ( v1_partfun1 @ E @ A )
        & ( r1_partfun1 @ C @ E )
        & ( r1_partfun1 @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r1_partfun1 @ X8 @ X6 )
      | ~ ( zip_tseitin_1 @ X6 @ X8 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_2 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( r1_partfun1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_3 @ B @ A ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [E: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ B @ A )
     => ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ~ ( ( zip_tseitin_3 @ B @ A )
              & ( r1_partfun1 @ C @ D )
              & ! [E: $i] :
                  ( zip_tseitin_2 @ E @ D @ C @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( r1_partfun1 @ X20 @ X17 )
      | ~ ( zip_tseitin_2 @ ( sk_E @ X17 @ X20 @ X19 @ X18 ) @ X17 @ X20 @ X19 @ X18 )
      | ~ ( zip_tseitin_3 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( zip_tseitin_3 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( zip_tseitin_3 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X10 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_1 @ X10 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r1_partfun1 @ X9 @ X6 )
      | ~ ( zip_tseitin_1 @ X6 @ X8 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_2 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( r1_partfun1 @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X10 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( r1_partfun1 @ X20 @ X17 )
      | ~ ( zip_tseitin_2 @ ( sk_E @ X17 @ X20 @ X19 @ X18 ) @ X17 @ X20 @ X19 @ X18 )
      | ~ ( zip_tseitin_3 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( zip_tseitin_3 @ sk_B @ k1_xboole_0 )
        | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_3 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X15: $i] :
      ( zip_tseitin_3 @ X15 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_partfun1 @ sk_C @ sk_D )
      | ( zip_tseitin_0 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( zip_tseitin_0 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('46',plain,(
    ! [X21: $i] :
      ( ~ ( r1_partfun1 @ sk_D @ X21 )
      | ~ ( r1_partfun1 @ sk_C @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X21 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
        | ~ ( r1_partfun1 @ sk_C @ X0 )
        | ~ ( r1_partfun1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ sk_B )
        | ~ ( r1_partfun1 @ sk_C @ X0 )
        | ~ ( r1_partfun1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
      | ~ ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_2 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( r1_partfun1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_partfun1 @ sk_C @ sk_D )
      | ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( zip_tseitin_0 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_funct_1 @ X3 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('61',plain,
    ( ( v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','58','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('65',plain,
    ( ( ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
      | ~ ( v1_partfun1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_1 @ X10 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v1_partfun1 @ X6 @ X7 )
      | ~ ( zip_tseitin_1 @ X6 @ X8 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_2 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( v1_partfun1 @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( v1_partfun1 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_partfun1 @ sk_C @ sk_D )
      | ( v1_partfun1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_partfun1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('77',plain,
    ( ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','75','76'])).

thf('78',plain,
    ( ~ ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','77'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( zip_tseitin_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ k1_xboole_0 ) @ X2 @ sk_C @ X1 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ k1_xboole_0 ) @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf('81',plain,
    ( ( ~ ( r1_partfun1 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('87',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','88'])).

thf('90',plain,
    ( ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ( zip_tseitin_0 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','89'])).

thf('91',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    zip_tseitin_0 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('95',plain,(
    m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X21: $i] :
      ( ~ ( r1_partfun1 @ sk_D @ X21 )
      | ~ ( r1_partfun1 @ sk_C @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X21 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    zip_tseitin_0 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('99',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_funct_1 @ X3 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('100',plain,(
    v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,(
    m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('104',plain,
    ( ( v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_2 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( v1_partfun1 @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','87'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_partfun1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    v1_funct_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('116',plain,(
    v1_funct_2 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['104','114','115'])).

thf('117',plain,
    ( ~ ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_2 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( r1_partfun1 @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( zip_tseitin_2 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ X0 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','87'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ X0 @ ( sk_E @ sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r1_partfun1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ~ ( r1_partfun1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','127'])).

thf('129',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','128'])).

thf('130',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','87'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).


%------------------------------------------------------------------------------
