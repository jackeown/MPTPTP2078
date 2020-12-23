%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d1fs79pHe9

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:15 EST 2020

% Result     : Theorem 26.87s
% Output     : Refutation 26.87s
% Verified   : 
% Statistics : Number of formulae       :  304 (19916 expanded)
%              Number of leaves         :   52 (5509 expanded)
%              Depth                    :   38
%              Number of atoms          : 2582 (308168 expanded)
%              Number of equality atoms :  139 (23962 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_6_type,type,(
    zip_tseitin_6: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

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

thf(zf_stmt_0,axiom,(
    ! [E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_3 @ E @ B @ A )
       => ~ ( zip_tseitin_4 @ E @ D @ C @ A ) )
     => ( zip_tseitin_5 @ E @ D @ C @ B @ A ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( zip_tseitin_4 @ X48 @ X49 @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_4 @ E @ D @ C @ A )
     => ( ( v1_partfun1 @ E @ A )
        & ( r1_partfun1 @ C @ E )
        & ( r1_partfun1 @ D @ E ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( r1_partfun1 @ X47 @ X44 )
      | ~ ( zip_tseitin_4 @ X44 @ X46 @ X47 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_5 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( r1_partfun1 @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf(zf_stmt_2,negated_conjecture,(
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

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( zip_tseitin_3 @ X48 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(zf_stmt_3,type,(
    zip_tseitin_6: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_6 @ B @ A ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_5: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [E: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ E @ B @ A )
     => ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ~ ( ( zip_tseitin_6 @ B @ A )
              & ( r1_partfun1 @ C @ D )
              & ! [E: $i] :
                  ( zip_tseitin_5 @ E @ D @ C @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( r1_partfun1 @ X58 @ X55 )
      | ~ ( zip_tseitin_5 @ ( sk_E @ X55 @ X58 @ X57 @ X56 ) @ X55 @ X58 @ X57 @ X56 )
      | ~ ( zip_tseitin_6 @ X57 @ X56 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( zip_tseitin_6 @ sk_B @ sk_A_1 )
      | ~ ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_D_1 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( zip_tseitin_6 @ sk_B @ sk_A_1 )
      | ~ ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_D_1 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_6 @ X53 @ X54 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_6 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(t148_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ~ ( ! [D: $i] :
              ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                & ( v1_funct_2 @ D @ A @ B )
                & ( v1_funct_1 @ D ) )
             => ~ ( r1_partfun1 @ C @ D ) )
          & ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_10,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_2 @ B @ A ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf(zf_stmt_11,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ B @ A )
       => ~ ( r1_partfun1 @ C @ D ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( zip_tseitin_0 @ X32 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(zf_stmt_12,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_13,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_14,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_15,axiom,(
    ! [D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ B @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_16,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( zip_tseitin_2 @ B @ A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_2 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X40 @ X38 @ X39 ) @ X40 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_D_1 @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_D_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( sk_A_1 = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( zip_tseitin_0 @ X32 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('35',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_2 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X40 @ X38 @ X39 ) @ X40 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_C_1 @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_C_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ sk_B @ sk_A_1 ) @ sk_C_1 @ sk_B @ sk_A_1 )
      | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('43',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('45',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('47',plain,(
    ! [X36: $i] :
      ( zip_tseitin_2 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','47'])).

thf('49',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('51',plain,
    ( ( v1_funct_2 @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('54',plain,
    ( ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,
    ( ( r1_tarski @ ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('60',plain,
    ( ( ( sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('63',plain,(
    ! [X59: $i] :
      ( ~ ( r1_partfun1 @ sk_D_1 @ X59 )
      | ~ ( r1_partfun1 @ sk_C_1 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X59 @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ sk_A_1 @ sk_B )
        | ~ ( r1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( r1_partfun1 @ sk_D_1 @ X0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('66',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('67',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('69',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('70',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,
    ( ( r1_tarski @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('76',plain,
    ( ( sk_D_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ sk_B )
        | ~ ( r1_partfun1 @ k1_xboole_0 @ X0 )
        | ~ ( r1_partfun1 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66','67','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ k1_xboole_0 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ sk_B )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','78'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('80',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(rc1_funct_1,axiom,(
    ? [A: $i] :
      ( ( v1_funct_1 @ A )
      & ( v1_relat_1 @ A ) ) )).

thf('81',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_funct_1])).

thf('82',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('83',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_funct_1])).

thf('87',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('89',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('90',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_D_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('92',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80','87','92'])).

thf('94',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','95'])).

thf('97',plain,(
    zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ),
    inference('simplify_reflect-',[status(thm)],['22','96'])).

thf('98',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('99',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    r1_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('102',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
      = ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
      | ( zip_tseitin_6 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
        = ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','103'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('105',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_6 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
        = ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('108',plain,(
    ! [X59: $i] :
      ( ~ ( r1_partfun1 @ sk_D_1 @ X59 )
      | ~ ( r1_partfun1 @ sk_C_1 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X59 @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_A_1 @ sk_B )
    | ~ ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
    | ~ ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ),
    inference('simplify_reflect-',[status(thm)],['22','96'])).

thf('111',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_funct_1 @ X29 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('112',plain,(
    v1_funct_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ),
    inference('simplify_reflect-',[status(thm)],['22','96'])).

thf('114',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('115',plain,(
    v1_funct_2 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_A_1 @ sk_B ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
    | ~ ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['109','112','115'])).

thf('117',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('118',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_2 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( r1_partfun1 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('121',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) @ sk_D_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('122',plain,
    ( ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','95'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('130',plain,(
    ! [X36: $i] :
      ( zip_tseitin_2 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('131',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( r1_partfun1 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('132',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('133',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_2 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X40 @ X38 @ X39 ) @ X40 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_partfun1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( r1_partfun1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( zip_tseitin_0 @ X32 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('140',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('142',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_2 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X40 @ X38 @ X39 ) @ X40 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_2 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','146'])).

thf('148',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('149',plain,(
    ! [X36: $i] :
      ( zip_tseitin_2 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('150',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('151',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('152',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149','150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','152'])).

thf('154',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('155',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('159',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['138','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ k1_xboole_0 @ X0 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup+',[status(thm)],['129','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_partfun1 @ X0 @ X1 )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
      | ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup+',[status(thm)],['128','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) )
      | ( r1_partfun1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    r1_partfun1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ),
    inference(condensation,[status(thm)],['165'])).

thf('167',plain,(
    ~ ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['116','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
      | ( zip_tseitin_6 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_6 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('170',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('171',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( zip_tseitin_0 @ X32 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('172',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_C_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('173',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','95'])).

thf('176',plain,(
    zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_15])).

thf('178',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('180',plain,(
    r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('182',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
      = ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) )
      | ( zip_tseitin_6 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','182'])).

thf('184',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_6 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B )
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_2 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('187',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X32 @ X33 @ X34 @ X35 )
      | ( r1_partfun1 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('188',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_C_1 @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('189',plain,
    ( ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) )
    | ~ ( zip_tseitin_2 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X6 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','95'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['193','194'])).

thf('197',plain,(
    r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['138','161'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ k1_xboole_0 @ X0 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_partfun1 @ X0 @ X1 )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup+',[status(thm)],['195','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) )
      | ( r1_partfun1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    r1_partfun1 @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A_1 ) ),
    inference(condensation,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
      | ( zip_tseitin_6 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['185','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( zip_tseitin_6 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['168','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_D_1 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','204'])).

thf('206',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D_1 )
    | ( zip_tseitin_3 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['3','205'])).

thf('207',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('208',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('209',plain,(
    zip_tseitin_3 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( zip_tseitin_3 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('211',plain,(
    m1_subset_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X59: $i] :
      ( ~ ( r1_partfun1 @ sk_D_1 @ X59 )
      | ~ ( r1_partfun1 @ sk_C_1 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X59 @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('213',plain,
    ( ~ ( v1_funct_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 @ sk_B )
    | ~ ( r1_partfun1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) )
    | ~ ( r1_partfun1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    zip_tseitin_3 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('215',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_1 @ X41 )
      | ~ ( zip_tseitin_3 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('216',plain,(
    v1_funct_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('218',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( zip_tseitin_4 @ X48 @ X49 @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( r1_partfun1 @ X46 @ X44 )
      | ~ ( zip_tseitin_4 @ X44 @ X46 @ X47 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('220',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_5 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( r1_partfun1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_D_1 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','203'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D_1 )
    | ( r1_partfun1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['217','222'])).

thf('224',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('225',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('226',plain,(
    r1_partfun1 @ sk_D_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,
    ( ~ ( v1_funct_2 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 @ sk_B )
    | ~ ( r1_partfun1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['213','216','226'])).

thf('228',plain,(
    m1_subset_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf(t131_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('229',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X24 )
      | ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t131_funct_2])).

thf('230',plain,
    ( ~ ( v1_funct_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) )
    | ( v1_funct_2 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 @ sk_B )
    | ~ ( v1_partfun1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v1_funct_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('232',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('233',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( zip_tseitin_4 @ X48 @ X49 @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v1_partfun1 @ X44 @ X45 )
      | ~ ( zip_tseitin_4 @ X44 @ X46 @ X47 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_5 @ X3 @ X2 @ X1 @ X4 @ X0 )
      | ( v1_partfun1 @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_D_1 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','203'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D_1 )
    | ( v1_partfun1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['232','237'])).

thf('239',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('240',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('241',plain,(
    v1_partfun1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    v1_funct_2 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ sk_A_1 @ sk_B ),
    inference(demod,[status(thm)],['230','231','241'])).

thf('243',plain,(
    ~ ( r1_partfun1 @ sk_C_1 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['227','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1 ) @ X2 @ sk_C_1 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['2','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( zip_tseitin_5 @ ( sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1 ) @ sk_D_1 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','203'])).

thf('246',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('248',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('249',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('250',plain,(
    $false ),
    inference(demod,[status(thm)],['246','247','248','249'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d1fs79pHe9
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 26.87/27.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 26.87/27.15  % Solved by: fo/fo7.sh
% 26.87/27.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.87/27.15  % done 14582 iterations in 26.683s
% 26.87/27.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 26.87/27.15  % SZS output start Refutation
% 26.87/27.15  thf(sk_B_type, type, sk_B: $i).
% 26.87/27.15  thf(zip_tseitin_6_type, type, zip_tseitin_6: $i > $i > $o).
% 26.87/27.15  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 26.87/27.15  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 26.87/27.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.87/27.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.87/27.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 26.87/27.15  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $i > $i > $o).
% 26.87/27.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 26.87/27.15  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 26.87/27.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 26.87/27.15  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 26.87/27.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 26.87/27.15  thf(sk_A_type, type, sk_A: $i).
% 26.87/27.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 26.87/27.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.87/27.15  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $i > $i > $o).
% 26.87/27.15  thf(sk_D_1_type, type, sk_D_1: $i).
% 26.87/27.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 26.87/27.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.87/27.15  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 26.87/27.15  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 26.87/27.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 26.87/27.15  thf(sk_A_1_type, type, sk_A_1: $i).
% 26.87/27.15  thf(t162_partfun1, axiom,
% 26.87/27.15    (![A:$i,B:$i,C:$i]:
% 26.87/27.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.87/27.15         ( v1_funct_1 @ C ) ) =>
% 26.87/27.15       ( ![D:$i]:
% 26.87/27.15         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.87/27.15             ( v1_funct_1 @ D ) ) =>
% 26.87/27.15           ( ~( ( ![E:$i]:
% 26.87/27.15                  ( ( ( m1_subset_1 @
% 26.87/27.15                        E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.87/27.15                      ( v1_funct_1 @ E ) ) =>
% 26.87/27.15                    ( ~( ( r1_partfun1 @ D @ E ) & ( r1_partfun1 @ C @ E ) & 
% 26.87/27.15                         ( v1_partfun1 @ E @ A ) ) ) ) ) & 
% 26.87/27.15                ( r1_partfun1 @ C @ D ) & 
% 26.87/27.15                ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 26.87/27.15  thf(zf_stmt_0, axiom,
% 26.87/27.15    (![E:$i,D:$i,C:$i,B:$i,A:$i]:
% 26.87/27.15     ( ( ( zip_tseitin_3 @ E @ B @ A ) =>
% 26.87/27.15         ( ~( zip_tseitin_4 @ E @ D @ C @ A ) ) ) =>
% 26.87/27.15       ( zip_tseitin_5 @ E @ D @ C @ B @ A ) ))).
% 26.87/27.15  thf('0', plain,
% 26.87/27.15      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 26.87/27.15         ((zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52)
% 26.87/27.15          | (zip_tseitin_4 @ X48 @ X49 @ X50 @ X52))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.87/27.15  thf(zf_stmt_1, axiom,
% 26.87/27.15    (![E:$i,D:$i,C:$i,A:$i]:
% 26.87/27.15     ( ( zip_tseitin_4 @ E @ D @ C @ A ) =>
% 26.87/27.15       ( ( v1_partfun1 @ E @ A ) & ( r1_partfun1 @ C @ E ) & 
% 26.87/27.15         ( r1_partfun1 @ D @ E ) ) ))).
% 26.87/27.15  thf('1', plain,
% 26.87/27.15      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 26.87/27.15         ((r1_partfun1 @ X47 @ X44) | ~ (zip_tseitin_4 @ X44 @ X46 @ X47 @ X45))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.87/27.15  thf('2', plain,
% 26.87/27.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.87/27.15         ((zip_tseitin_5 @ X3 @ X2 @ X1 @ X4 @ X0) | (r1_partfun1 @ X1 @ X3))),
% 26.87/27.15      inference('sup-', [status(thm)], ['0', '1'])).
% 26.87/27.15  thf(t154_funct_2, conjecture,
% 26.87/27.15    (![A:$i,B:$i,C:$i]:
% 26.87/27.15     ( ( ( v1_funct_1 @ C ) & 
% 26.87/27.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15       ( ![D:$i]:
% 26.87/27.15         ( ( ( v1_funct_1 @ D ) & 
% 26.87/27.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15           ( ~( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) & 
% 26.87/27.15                ( r1_partfun1 @ C @ D ) & 
% 26.87/27.15                ( ![E:$i]:
% 26.87/27.15                  ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 26.87/27.15                      ( m1_subset_1 @
% 26.87/27.15                        E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15                    ( ~( ( r1_partfun1 @ C @ E ) & ( r1_partfun1 @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 26.87/27.15  thf(zf_stmt_2, negated_conjecture,
% 26.87/27.15    (~( ![A:$i,B:$i,C:$i]:
% 26.87/27.15        ( ( ( v1_funct_1 @ C ) & 
% 26.87/27.15            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15          ( ![D:$i]:
% 26.87/27.15            ( ( ( v1_funct_1 @ D ) & 
% 26.87/27.15                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15              ( ~( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) & 
% 26.87/27.15                   ( r1_partfun1 @ C @ D ) & 
% 26.87/27.15                   ( ![E:$i]:
% 26.87/27.15                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 26.87/27.15                         ( m1_subset_1 @
% 26.87/27.15                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15                       ( ~( ( r1_partfun1 @ C @ E ) & ( r1_partfun1 @ D @ E ) ) ) ) ) ) ) ) ) ) )),
% 26.87/27.15    inference('cnf.neg', [status(esa)], [t154_funct_2])).
% 26.87/27.15  thf('3', plain,
% 26.87/27.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.15  thf('4', plain,
% 26.87/27.15      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 26.87/27.15         ((zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52)
% 26.87/27.15          | (zip_tseitin_3 @ X48 @ X51 @ X52))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.87/27.15  thf('5', plain,
% 26.87/27.15      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.15  thf(zf_stmt_3, type, zip_tseitin_6 : $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_4, axiom,
% 26.87/27.15    (![B:$i,A:$i]:
% 26.87/27.15     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 26.87/27.15       ( zip_tseitin_6 @ B @ A ) ))).
% 26.87/27.15  thf(zf_stmt_5, type, zip_tseitin_5 : $i > $i > $i > $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_6, type, zip_tseitin_4 : $i > $i > $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_8, axiom,
% 26.87/27.15    (![E:$i,B:$i,A:$i]:
% 26.87/27.15     ( ( zip_tseitin_3 @ E @ B @ A ) =>
% 26.87/27.15       ( ( v1_funct_1 @ E ) & 
% 26.87/27.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 26.87/27.15  thf(zf_stmt_9, axiom,
% 26.87/27.15    (![A:$i,B:$i,C:$i]:
% 26.87/27.15     ( ( ( v1_funct_1 @ C ) & 
% 26.87/27.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15       ( ![D:$i]:
% 26.87/27.15         ( ( ( v1_funct_1 @ D ) & 
% 26.87/27.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15           ( ~( ( zip_tseitin_6 @ B @ A ) & ( r1_partfun1 @ C @ D ) & 
% 26.87/27.15                ( ![E:$i]: ( zip_tseitin_5 @ E @ D @ C @ B @ A ) ) ) ) ) ) ))).
% 26.87/27.15  thf('6', plain,
% 26.87/27.15      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 26.87/27.15         (~ (v1_funct_1 @ X55)
% 26.87/27.15          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 26.87/27.15          | ~ (r1_partfun1 @ X58 @ X55)
% 26.87/27.15          | ~ (zip_tseitin_5 @ (sk_E @ X55 @ X58 @ X57 @ X56) @ X55 @ X58 @ 
% 26.87/27.15               X57 @ X56)
% 26.87/27.15          | ~ (zip_tseitin_6 @ X57 @ X56)
% 26.87/27.15          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 26.87/27.15          | ~ (v1_funct_1 @ X58))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_9])).
% 26.87/27.15  thf('7', plain,
% 26.87/27.15      (![X0 : $i]:
% 26.87/27.15         (~ (v1_funct_1 @ X0)
% 26.87/27.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.15          | ~ (zip_tseitin_6 @ sk_B @ sk_A_1)
% 26.87/27.15          | ~ (zip_tseitin_5 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_D_1 @ 
% 26.87/27.15               X0 @ sk_B @ sk_A_1)
% 26.87/27.15          | ~ (r1_partfun1 @ X0 @ sk_D_1)
% 26.87/27.15          | ~ (v1_funct_1 @ sk_D_1))),
% 26.87/27.15      inference('sup-', [status(thm)], ['5', '6'])).
% 26.87/27.15  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.15  thf('9', plain,
% 26.87/27.15      (![X0 : $i]:
% 26.87/27.15         (~ (v1_funct_1 @ X0)
% 26.87/27.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.15          | ~ (zip_tseitin_6 @ sk_B @ sk_A_1)
% 26.87/27.15          | ~ (zip_tseitin_5 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_D_1 @ 
% 26.87/27.15               X0 @ sk_B @ sk_A_1)
% 26.87/27.15          | ~ (r1_partfun1 @ X0 @ sk_D_1))),
% 26.87/27.15      inference('demod', [status(thm)], ['7', '8'])).
% 26.87/27.15  thf('10', plain,
% 26.87/27.15      (![X53 : $i, X54 : $i]:
% 26.87/27.15         ((zip_tseitin_6 @ X53 @ X54) | ((X53) = (k1_xboole_0)))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_4])).
% 26.87/27.15  thf(t113_zfmisc_1, axiom,
% 26.87/27.15    (![A:$i,B:$i]:
% 26.87/27.15     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 26.87/27.15       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 26.87/27.15  thf('11', plain,
% 26.87/27.15      (![X6 : $i, X7 : $i]:
% 26.87/27.15         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 26.87/27.15      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 26.87/27.15  thf('12', plain,
% 26.87/27.15      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 26.87/27.15      inference('simplify', [status(thm)], ['11'])).
% 26.87/27.15  thf('13', plain,
% 26.87/27.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.87/27.15         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_6 @ X0 @ X2))),
% 26.87/27.15      inference('sup+', [status(thm)], ['10', '12'])).
% 26.87/27.15  thf(t148_funct_2, axiom,
% 26.87/27.15    (![A:$i,B:$i,C:$i]:
% 26.87/27.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.87/27.15         ( v1_funct_1 @ C ) ) =>
% 26.87/27.15       ( ~( ( ![D:$i]:
% 26.87/27.15              ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.87/27.15                  ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 26.87/27.15                ( ~( r1_partfun1 @ C @ D ) ) ) ) & 
% 26.87/27.15            ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 26.87/27.15  thf(zf_stmt_10, axiom,
% 26.87/27.15    (![B:$i,A:$i]:
% 26.87/27.15     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 26.87/27.15       ( zip_tseitin_2 @ B @ A ) ))).
% 26.87/27.15  thf('14', plain,
% 26.87/27.15      (![X36 : $i, X37 : $i]:
% 26.87/27.15         ((zip_tseitin_2 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_10])).
% 26.87/27.15  thf(zf_stmt_11, axiom,
% 26.87/27.15    (![D:$i,C:$i,B:$i,A:$i]:
% 26.87/27.15     ( ( ( zip_tseitin_0 @ D @ B @ A ) => ( ~( r1_partfun1 @ C @ D ) ) ) =>
% 26.87/27.15       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 26.87/27.15  thf('15', plain,
% 26.87/27.15      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.15         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35)
% 26.87/27.15          | (zip_tseitin_0 @ X32 @ X34 @ X35))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.15  thf('16', plain,
% 26.87/27.15      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.15  thf(zf_stmt_12, type, zip_tseitin_2 : $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_13, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_14, type, zip_tseitin_0 : $i > $i > $i > $o).
% 26.87/27.15  thf(zf_stmt_15, axiom,
% 26.87/27.15    (![D:$i,B:$i,A:$i]:
% 26.87/27.15     ( ( zip_tseitin_0 @ D @ B @ A ) =>
% 26.87/27.15       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 26.87/27.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 26.87/27.15  thf(zf_stmt_16, axiom,
% 26.87/27.15    (![A:$i,B:$i,C:$i]:
% 26.87/27.15     ( ( ( v1_funct_1 @ C ) & 
% 26.87/27.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.15       ( ~( ( zip_tseitin_2 @ B @ A ) & 
% 26.87/27.15            ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ))).
% 26.87/27.15  thf('17', plain,
% 26.87/27.15      (![X38 : $i, X39 : $i, X40 : $i]:
% 26.87/27.15         (~ (zip_tseitin_2 @ X38 @ X39)
% 26.87/27.15          | ~ (v1_funct_1 @ X40)
% 26.87/27.15          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 26.87/27.15          | ~ (zip_tseitin_1 @ (sk_D @ X40 @ X38 @ X39) @ X40 @ X38 @ X39))),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_16])).
% 26.87/27.15  thf('18', plain,
% 26.87/27.15      ((~ (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_D_1 @ sk_B @ 
% 26.87/27.15           sk_A_1)
% 26.87/27.15        | ~ (v1_funct_1 @ sk_D_1)
% 26.87/27.15        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.15      inference('sup-', [status(thm)], ['16', '17'])).
% 26.87/27.15  thf('19', plain, ((v1_funct_1 @ sk_D_1)),
% 26.87/27.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.15  thf('20', plain,
% 26.87/27.15      ((~ (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_D_1 @ sk_B @ 
% 26.87/27.16           sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['18', '19'])).
% 26.87/27.16  thf('21', plain,
% 26.87/27.16      (((zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['15', '20'])).
% 26.87/27.16  thf('22', plain,
% 26.87/27.16      ((((sk_B) = (k1_xboole_0))
% 26.87/27.16        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['14', '21'])).
% 26.87/27.16  thf('23', plain, ((((sk_A_1) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('24', plain,
% 26.87/27.16      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('25', plain,
% 26.87/27.16      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.16         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35)
% 26.87/27.16          | (zip_tseitin_0 @ X32 @ X34 @ X35))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.16  thf('26', plain,
% 26.87/27.16      (![X6 : $i, X7 : $i]:
% 26.87/27.16         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 26.87/27.16  thf('27', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('28', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('29', plain,
% 26.87/27.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('30', plain,
% 26.87/27.16      (((m1_subset_1 @ sk_C_1 @ 
% 26.87/27.16         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup+', [status(thm)], ['28', '29'])).
% 26.87/27.16  thf('31', plain,
% 26.87/27.16      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup+', [status(thm)], ['27', '30'])).
% 26.87/27.16  thf(t3_subset, axiom,
% 26.87/27.16    (![A:$i,B:$i]:
% 26.87/27.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 26.87/27.16  thf('32', plain,
% 26.87/27.16      (![X13 : $i, X14 : $i]:
% 26.87/27.16         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('33', plain,
% 26.87/27.16      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['31', '32'])).
% 26.87/27.16  thf(t3_xboole_1, axiom,
% 26.87/27.16    (![A:$i]:
% 26.87/27.16     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 26.87/27.16  thf('34', plain,
% 26.87/27.16      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_xboole_1])).
% 26.87/27.16  thf('35', plain,
% 26.87/27.16      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['33', '34'])).
% 26.87/27.16  thf('36', plain,
% 26.87/27.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('37', plain,
% 26.87/27.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 26.87/27.16         (~ (zip_tseitin_2 @ X38 @ X39)
% 26.87/27.16          | ~ (v1_funct_1 @ X40)
% 26.87/27.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 26.87/27.16          | ~ (zip_tseitin_1 @ (sk_D @ X40 @ X38 @ X39) @ X40 @ X38 @ X39))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_16])).
% 26.87/27.16  thf('38', plain,
% 26.87/27.16      ((~ (zip_tseitin_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_C_1 @ sk_B @ 
% 26.87/27.16           sk_A_1)
% 26.87/27.16        | ~ (v1_funct_1 @ sk_C_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['36', '37'])).
% 26.87/27.16  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('40', plain,
% 26.87/27.16      ((~ (zip_tseitin_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_C_1 @ sk_B @ 
% 26.87/27.16           sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['38', '39'])).
% 26.87/27.16  thf('41', plain,
% 26.87/27.16      (((~ (zip_tseitin_1 @ (sk_D @ k1_xboole_0 @ sk_B @ sk_A_1) @ sk_C_1 @ 
% 26.87/27.16            sk_B @ sk_A_1)
% 26.87/27.16         | ~ (zip_tseitin_2 @ sk_B @ sk_A_1)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['35', '40'])).
% 26.87/27.16  thf('42', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('43', plain,
% 26.87/27.16      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['33', '34'])).
% 26.87/27.16  thf('44', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('45', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('46', plain,
% 26.87/27.16      (![X36 : $i, X37 : $i]:
% 26.87/27.16         ((zip_tseitin_2 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_10])).
% 26.87/27.16  thf('47', plain, (![X36 : $i]: (zip_tseitin_2 @ X36 @ k1_xboole_0)),
% 26.87/27.16      inference('simplify', [status(thm)], ['46'])).
% 26.87/27.16  thf('48', plain,
% 26.87/27.16      ((~ (zip_tseitin_1 @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 26.87/27.16           k1_xboole_0 @ sk_B @ k1_xboole_0))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '47'])).
% 26.87/27.16  thf('49', plain,
% 26.87/27.16      (((zip_tseitin_0 @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ sk_B @ 
% 26.87/27.16         k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['25', '48'])).
% 26.87/27.16  thf('50', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((v1_funct_2 @ X29 @ X31 @ X30) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('51', plain,
% 26.87/27.16      (((v1_funct_2 @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 26.87/27.16         k1_xboole_0 @ sk_B)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['49', '50'])).
% 26.87/27.16  thf('52', plain,
% 26.87/27.16      (((zip_tseitin_0 @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ sk_B @ 
% 26.87/27.16         k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['25', '48'])).
% 26.87/27.16  thf('53', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 26.87/27.16          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('54', plain,
% 26.87/27.16      (((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 26.87/27.16         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['52', '53'])).
% 26.87/27.16  thf('55', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('56', plain,
% 26.87/27.16      (((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 26.87/27.16         (k1_zfmisc_1 @ k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('demod', [status(thm)], ['54', '55'])).
% 26.87/27.16  thf('57', plain,
% 26.87/27.16      (![X13 : $i, X14 : $i]:
% 26.87/27.16         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('58', plain,
% 26.87/27.16      (((r1_tarski @ (sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) @ k1_xboole_0))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['56', '57'])).
% 26.87/27.16  thf('59', plain,
% 26.87/27.16      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_xboole_1])).
% 26.87/27.16  thf('60', plain,
% 26.87/27.16      ((((sk_D @ k1_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['58', '59'])).
% 26.87/27.16  thf('61', plain,
% 26.87/27.16      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('demod', [status(thm)], ['51', '60'])).
% 26.87/27.16  thf('62', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('63', plain,
% 26.87/27.16      (![X59 : $i]:
% 26.87/27.16         (~ (r1_partfun1 @ sk_D_1 @ X59)
% 26.87/27.16          | ~ (r1_partfun1 @ sk_C_1 @ X59)
% 26.87/27.16          | ~ (m1_subset_1 @ X59 @ 
% 26.87/27.16               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (v1_funct_2 @ X59 @ sk_A_1 @ sk_B)
% 26.87/27.16          | ~ (v1_funct_1 @ X59))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('64', plain,
% 26.87/27.16      ((![X0 : $i]:
% 26.87/27.16          (~ (m1_subset_1 @ X0 @ 
% 26.87/27.16              (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))
% 26.87/27.16           | ~ (v1_funct_1 @ X0)
% 26.87/27.16           | ~ (v1_funct_2 @ X0 @ sk_A_1 @ sk_B)
% 26.87/27.16           | ~ (r1_partfun1 @ sk_C_1 @ X0)
% 26.87/27.16           | ~ (r1_partfun1 @ sk_D_1 @ X0)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['62', '63'])).
% 26.87/27.16  thf('65', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('66', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('67', plain,
% 26.87/27.16      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['33', '34'])).
% 26.87/27.16  thf('68', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('69', plain,
% 26.87/27.16      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('70', plain,
% 26.87/27.16      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('71', plain,
% 26.87/27.16      (((m1_subset_1 @ sk_D_1 @ 
% 26.87/27.16         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup+', [status(thm)], ['69', '70'])).
% 26.87/27.16  thf('72', plain,
% 26.87/27.16      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup+', [status(thm)], ['68', '71'])).
% 26.87/27.16  thf('73', plain,
% 26.87/27.16      (![X13 : $i, X14 : $i]:
% 26.87/27.16         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('74', plain,
% 26.87/27.16      (((r1_tarski @ sk_D_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['72', '73'])).
% 26.87/27.16  thf('75', plain,
% 26.87/27.16      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_xboole_1])).
% 26.87/27.16  thf('76', plain,
% 26.87/27.16      ((((sk_D_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['74', '75'])).
% 26.87/27.16  thf('77', plain,
% 26.87/27.16      ((![X0 : $i]:
% 26.87/27.16          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 26.87/27.16           | ~ (v1_funct_1 @ X0)
% 26.87/27.16           | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ sk_B)
% 26.87/27.16           | ~ (r1_partfun1 @ k1_xboole_0 @ X0)
% 26.87/27.16           | ~ (r1_partfun1 @ k1_xboole_0 @ X0)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('demod', [status(thm)], ['64', '65', '66', '67', '76'])).
% 26.87/27.16  thf('78', plain,
% 26.87/27.16      ((![X0 : $i]:
% 26.87/27.16          (~ (r1_partfun1 @ k1_xboole_0 @ X0)
% 26.87/27.16           | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ sk_B)
% 26.87/27.16           | ~ (v1_funct_1 @ X0)
% 26.87/27.16           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('simplify', [status(thm)], ['77'])).
% 26.87/27.16  thf('79', plain,
% 26.87/27.16      (((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 26.87/27.16         | ~ (v1_funct_1 @ k1_xboole_0)
% 26.87/27.16         | ~ (r1_partfun1 @ k1_xboole_0 @ k1_xboole_0)))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['61', '78'])).
% 26.87/27.16  thf(t4_subset_1, axiom,
% 26.87/27.16    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 26.87/27.16  thf('80', plain,
% 26.87/27.16      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 26.87/27.16      inference('cnf', [status(esa)], [t4_subset_1])).
% 26.87/27.16  thf(rc1_funct_1, axiom,
% 26.87/27.16    (?[A:$i]: ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ))).
% 26.87/27.16  thf('81', plain, ((v1_funct_1 @ sk_A)),
% 26.87/27.16      inference('cnf', [status(esa)], [rc1_funct_1])).
% 26.87/27.16  thf('82', plain,
% 26.87/27.16      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 26.87/27.16      inference('cnf', [status(esa)], [t4_subset_1])).
% 26.87/27.16  thf(cc3_funct_1, axiom,
% 26.87/27.16    (![A:$i]:
% 26.87/27.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 26.87/27.16       ( ![B:$i]:
% 26.87/27.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 26.87/27.16  thf('83', plain,
% 26.87/27.16      (![X21 : $i, X22 : $i]:
% 26.87/27.16         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 26.87/27.16          | (v1_funct_1 @ X21)
% 26.87/27.16          | ~ (v1_funct_1 @ X22)
% 26.87/27.16          | ~ (v1_relat_1 @ X22))),
% 26.87/27.16      inference('cnf', [status(esa)], [cc3_funct_1])).
% 26.87/27.16  thf('84', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (v1_relat_1 @ X0)
% 26.87/27.16          | ~ (v1_funct_1 @ X0)
% 26.87/27.16          | (v1_funct_1 @ k1_xboole_0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['82', '83'])).
% 26.87/27.16  thf('85', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_A))),
% 26.87/27.16      inference('sup-', [status(thm)], ['81', '84'])).
% 26.87/27.16  thf('86', plain, ((v1_relat_1 @ sk_A)),
% 26.87/27.16      inference('cnf', [status(esa)], [rc1_funct_1])).
% 26.87/27.16  thf('87', plain, ((v1_funct_1 @ k1_xboole_0)),
% 26.87/27.16      inference('demod', [status(thm)], ['85', '86'])).
% 26.87/27.16  thf('88', plain,
% 26.87/27.16      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['33', '34'])).
% 26.87/27.16  thf('89', plain, ((r1_partfun1 @ sk_C_1 @ sk_D_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('90', plain,
% 26.87/27.16      (((r1_partfun1 @ k1_xboole_0 @ sk_D_1)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup+', [status(thm)], ['88', '89'])).
% 26.87/27.16  thf('91', plain,
% 26.87/27.16      ((((sk_D_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('sup-', [status(thm)], ['74', '75'])).
% 26.87/27.16  thf('92', plain,
% 26.87/27.16      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 26.87/27.16         <= ((((sk_A_1) = (k1_xboole_0))))),
% 26.87/27.16      inference('demod', [status(thm)], ['90', '91'])).
% 26.87/27.16  thf('93', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 26.87/27.16      inference('demod', [status(thm)], ['79', '80', '87', '92'])).
% 26.87/27.16  thf('94', plain,
% 26.87/27.16      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 26.87/27.16      inference('split', [status(esa)], ['23'])).
% 26.87/27.16  thf('95', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 26.87/27.16      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 26.87/27.16  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 26.87/27.16      inference('simpl_trail', [status(thm)], ['24', '95'])).
% 26.87/27.16  thf('97', plain,
% 26.87/27.16      ((zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['22', '96'])).
% 26.87/27.16  thf('98', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 26.87/27.16          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('99', plain,
% 26.87/27.16      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['97', '98'])).
% 26.87/27.16  thf('100', plain,
% 26.87/27.16      (![X13 : $i, X14 : $i]:
% 26.87/27.16         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('101', plain,
% 26.87/27.16      ((r1_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k2_zfmisc_1 @ sk_A_1 @ sk_B))),
% 26.87/27.16      inference('sup-', [status(thm)], ['99', '100'])).
% 26.87/27.16  thf(d10_xboole_0, axiom,
% 26.87/27.16    (![A:$i,B:$i]:
% 26.87/27.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 26.87/27.16  thf('102', plain,
% 26.87/27.16      (![X0 : $i, X2 : $i]:
% 26.87/27.16         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 26.87/27.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.87/27.16  thf('103', plain,
% 26.87/27.16      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A_1 @ sk_B) @ 
% 26.87/27.16           (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['101', '102'])).
% 26.87/27.16  thf('104', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (r1_tarski @ k1_xboole_0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | (zip_tseitin_6 @ sk_B @ X0)
% 26.87/27.16          | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['13', '103'])).
% 26.87/27.16  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 26.87/27.16  thf('105', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 26.87/27.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 26.87/27.16  thf('106', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((zip_tseitin_6 @ sk_B @ X0)
% 26.87/27.16          | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('demod', [status(thm)], ['104', '105'])).
% 26.87/27.16  thf('107', plain,
% 26.87/27.16      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['97', '98'])).
% 26.87/27.16  thf('108', plain,
% 26.87/27.16      (![X59 : $i]:
% 26.87/27.16         (~ (r1_partfun1 @ sk_D_1 @ X59)
% 26.87/27.16          | ~ (r1_partfun1 @ sk_C_1 @ X59)
% 26.87/27.16          | ~ (m1_subset_1 @ X59 @ 
% 26.87/27.16               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (v1_funct_2 @ X59 @ sk_A_1 @ sk_B)
% 26.87/27.16          | ~ (v1_funct_1 @ X59))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('109', plain,
% 26.87/27.16      ((~ (v1_funct_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (v1_funct_2 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_A_1 @ sk_B)
% 26.87/27.16        | ~ (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['107', '108'])).
% 26.87/27.16  thf('110', plain,
% 26.87/27.16      ((zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['22', '96'])).
% 26.87/27.16  thf('111', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((v1_funct_1 @ X29) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('112', plain, ((v1_funct_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['110', '111'])).
% 26.87/27.16  thf('113', plain,
% 26.87/27.16      ((zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['22', '96'])).
% 26.87/27.16  thf('114', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((v1_funct_2 @ X29 @ X31 @ X30) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('115', plain,
% 26.87/27.16      ((v1_funct_2 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_A_1 @ sk_B)),
% 26.87/27.16      inference('sup-', [status(thm)], ['113', '114'])).
% 26.87/27.16  thf('116', plain,
% 26.87/27.16      ((~ (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('demod', [status(thm)], ['109', '112', '115'])).
% 26.87/27.16  thf('117', plain,
% 26.87/27.16      (![X36 : $i, X37 : $i]:
% 26.87/27.16         ((zip_tseitin_2 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_10])).
% 26.87/27.16  thf('118', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('119', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.87/27.16         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_2 @ X0 @ X2))),
% 26.87/27.16      inference('sup+', [status(thm)], ['117', '118'])).
% 26.87/27.16  thf('120', plain,
% 26.87/27.16      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.16         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35) | (r1_partfun1 @ X33 @ X32))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.16  thf('121', plain,
% 26.87/27.16      ((~ (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1) @ sk_D_1 @ sk_B @ 
% 26.87/27.16           sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['18', '19'])).
% 26.87/27.16  thf('122', plain,
% 26.87/27.16      (((r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['120', '121'])).
% 26.87/27.16  thf('123', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['119', '122'])).
% 26.87/27.16  thf('124', plain,
% 26.87/27.16      (![X5 : $i, X6 : $i]:
% 26.87/27.16         (((X5) = (k1_xboole_0))
% 26.87/27.16          | ((X6) = (k1_xboole_0))
% 26.87/27.16          | ((k2_zfmisc_1 @ X6 @ X5) != (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 26.87/27.16  thf('125', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((k1_xboole_0) != (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | ((sk_B) = (k1_xboole_0))
% 26.87/27.16          | ((X0) = (k1_xboole_0)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['123', '124'])).
% 26.87/27.16  thf('126', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((X0) = (k1_xboole_0))
% 26.87/27.16          | ((sk_B) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('simplify', [status(thm)], ['125'])).
% 26.87/27.16  thf('127', plain, (((sk_B) != (k1_xboole_0))),
% 26.87/27.16      inference('simpl_trail', [status(thm)], ['24', '95'])).
% 26.87/27.16  thf('128', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((X0) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 26.87/27.16  thf('129', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((X0) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 26.87/27.16  thf('130', plain, (![X36 : $i]: (zip_tseitin_2 @ X36 @ k1_xboole_0)),
% 26.87/27.16      inference('simplify', [status(thm)], ['46'])).
% 26.87/27.16  thf('131', plain,
% 26.87/27.16      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.16         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35) | (r1_partfun1 @ X33 @ X32))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.16  thf('132', plain,
% 26.87/27.16      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 26.87/27.16      inference('cnf', [status(esa)], [t4_subset_1])).
% 26.87/27.16  thf('133', plain,
% 26.87/27.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 26.87/27.16         (~ (zip_tseitin_2 @ X38 @ X39)
% 26.87/27.16          | ~ (v1_funct_1 @ X40)
% 26.87/27.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 26.87/27.16          | ~ (zip_tseitin_1 @ (sk_D @ X40 @ X38 @ X39) @ X40 @ X38 @ X39))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_16])).
% 26.87/27.16  thf('134', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         (~ (zip_tseitin_1 @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ k1_xboole_0 @ 
% 26.87/27.16             X0 @ X1)
% 26.87/27.16          | ~ (v1_funct_1 @ k1_xboole_0)
% 26.87/27.16          | ~ (zip_tseitin_2 @ X0 @ X1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['132', '133'])).
% 26.87/27.16  thf('135', plain, ((v1_funct_1 @ k1_xboole_0)),
% 26.87/27.16      inference('demod', [status(thm)], ['85', '86'])).
% 26.87/27.16  thf('136', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         (~ (zip_tseitin_1 @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ k1_xboole_0 @ 
% 26.87/27.16             X0 @ X1)
% 26.87/27.16          | ~ (zip_tseitin_2 @ X0 @ X1))),
% 26.87/27.16      inference('demod', [status(thm)], ['134', '135'])).
% 26.87/27.16  thf('137', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         ((r1_partfun1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ X1 @ X0))
% 26.87/27.16          | ~ (zip_tseitin_2 @ X1 @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['131', '136'])).
% 26.87/27.16  thf('138', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (r1_partfun1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['130', '137'])).
% 26.87/27.16  thf('139', plain,
% 26.87/27.16      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.16         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35)
% 26.87/27.16          | (zip_tseitin_0 @ X32 @ X34 @ X35))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.16  thf('140', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('141', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 26.87/27.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.87/27.16  thf('142', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 26.87/27.16      inference('simplify', [status(thm)], ['141'])).
% 26.87/27.16  thf('143', plain,
% 26.87/27.16      (![X13 : $i, X15 : $i]:
% 26.87/27.16         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('144', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['142', '143'])).
% 26.87/27.16  thf('145', plain,
% 26.87/27.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 26.87/27.16         (~ (zip_tseitin_2 @ X38 @ X39)
% 26.87/27.16          | ~ (v1_funct_1 @ X40)
% 26.87/27.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 26.87/27.16          | ~ (zip_tseitin_1 @ (sk_D @ X40 @ X38 @ X39) @ X40 @ X38 @ X39))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_16])).
% 26.87/27.16  thf('146', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         (~ (zip_tseitin_1 @ (sk_D @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1) @ 
% 26.87/27.16             (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 26.87/27.16          | ~ (v1_funct_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 26.87/27.16          | ~ (zip_tseitin_2 @ X0 @ X1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['144', '145'])).
% 26.87/27.16  thf('147', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (zip_tseitin_1 @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 26.87/27.16             (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0)
% 26.87/27.16          | ~ (zip_tseitin_2 @ X0 @ k1_xboole_0)
% 26.87/27.16          | ~ (v1_funct_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['140', '146'])).
% 26.87/27.16  thf('148', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('149', plain, (![X36 : $i]: (zip_tseitin_2 @ X36 @ k1_xboole_0)),
% 26.87/27.16      inference('simplify', [status(thm)], ['46'])).
% 26.87/27.16  thf('150', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('151', plain, ((v1_funct_1 @ k1_xboole_0)),
% 26.87/27.16      inference('demod', [status(thm)], ['85', '86'])).
% 26.87/27.16  thf('152', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ~ (zip_tseitin_1 @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 26.87/27.16            k1_xboole_0 @ X0 @ k1_xboole_0)),
% 26.87/27.16      inference('demod', [status(thm)], ['147', '148', '149', '150', '151'])).
% 26.87/27.16  thf('153', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (zip_tseitin_0 @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X0 @ 
% 26.87/27.16          k1_xboole_0)),
% 26.87/27.16      inference('sup-', [status(thm)], ['139', '152'])).
% 26.87/27.16  thf('154', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 26.87/27.16          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('155', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 26.87/27.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['153', '154'])).
% 26.87/27.16  thf('156', plain,
% 26.87/27.16      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 26.87/27.16      inference('simplify', [status(thm)], ['26'])).
% 26.87/27.16  thf('157', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 26.87/27.16          (k1_zfmisc_1 @ k1_xboole_0))),
% 26.87/27.16      inference('demod', [status(thm)], ['155', '156'])).
% 26.87/27.16  thf('158', plain,
% 26.87/27.16      (![X13 : $i, X14 : $i]:
% 26.87/27.16         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('159', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (r1_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)),
% 26.87/27.16      inference('sup-', [status(thm)], ['157', '158'])).
% 26.87/27.16  thf('160', plain,
% 26.87/27.16      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_xboole_1])).
% 26.87/27.16  thf('161', plain,
% 26.87/27.16      (![X0 : $i]: ((sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['159', '160'])).
% 26.87/27.16  thf('162', plain, ((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 26.87/27.16      inference('demod', [status(thm)], ['138', '161'])).
% 26.87/27.16  thf('163', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((r1_partfun1 @ k1_xboole_0 @ X0)
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup+', [status(thm)], ['129', '162'])).
% 26.87/27.16  thf('164', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         ((r1_partfun1 @ X0 @ X1)
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | (r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup+', [status(thm)], ['128', '163'])).
% 26.87/27.16  thf('165', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         ((r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | (r1_partfun1 @ X0 @ X1))),
% 26.87/27.16      inference('simplify', [status(thm)], ['164'])).
% 26.87/27.16  thf('166', plain, ((r1_partfun1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('condensation', [status(thm)], ['165'])).
% 26.87/27.16  thf('167', plain,
% 26.87/27.16      (~ (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['116', '166'])).
% 26.87/27.16  thf('168', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (r1_partfun1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 26.87/27.16          | (zip_tseitin_6 @ sk_B @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['106', '167'])).
% 26.87/27.16  thf('169', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.87/27.16         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_6 @ X0 @ X2))),
% 26.87/27.16      inference('sup+', [status(thm)], ['10', '12'])).
% 26.87/27.16  thf('170', plain,
% 26.87/27.16      (![X36 : $i, X37 : $i]:
% 26.87/27.16         ((zip_tseitin_2 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_10])).
% 26.87/27.16  thf('171', plain,
% 26.87/27.16      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.16         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35)
% 26.87/27.16          | (zip_tseitin_0 @ X32 @ X34 @ X35))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.16  thf('172', plain,
% 26.87/27.16      ((~ (zip_tseitin_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_C_1 @ sk_B @ 
% 26.87/27.16           sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['38', '39'])).
% 26.87/27.16  thf('173', plain,
% 26.87/27.16      (((zip_tseitin_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['171', '172'])).
% 26.87/27.16  thf('174', plain,
% 26.87/27.16      ((((sk_B) = (k1_xboole_0))
% 26.87/27.16        | (zip_tseitin_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['170', '173'])).
% 26.87/27.16  thf('175', plain, (((sk_B) != (k1_xboole_0))),
% 26.87/27.16      inference('simpl_trail', [status(thm)], ['24', '95'])).
% 26.87/27.16  thf('176', plain,
% 26.87/27.16      ((zip_tseitin_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 26.87/27.16  thf('177', plain,
% 26.87/27.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.87/27.16         ((m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 26.87/27.16          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_15])).
% 26.87/27.16  thf('178', plain,
% 26.87/27.16      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['176', '177'])).
% 26.87/27.16  thf('179', plain,
% 26.87/27.16      (![X13 : $i, X14 : $i]:
% 26.87/27.16         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t3_subset])).
% 26.87/27.16  thf('180', plain,
% 26.87/27.16      ((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k2_zfmisc_1 @ sk_A_1 @ sk_B))),
% 26.87/27.16      inference('sup-', [status(thm)], ['178', '179'])).
% 26.87/27.16  thf('181', plain,
% 26.87/27.16      (![X0 : $i, X2 : $i]:
% 26.87/27.16         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 26.87/27.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.87/27.16  thf('182', plain,
% 26.87/27.16      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A_1 @ sk_B) @ 
% 26.87/27.16           (sk_D @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['180', '181'])).
% 26.87/27.16  thf('183', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (r1_tarski @ k1_xboole_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | (zip_tseitin_6 @ sk_B @ X0)
% 26.87/27.16          | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['169', '182'])).
% 26.87/27.16  thf('184', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 26.87/27.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 26.87/27.16  thf('185', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((zip_tseitin_6 @ sk_B @ X0)
% 26.87/27.16          | ((k2_zfmisc_1 @ sk_A_1 @ sk_B) = (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('demod', [status(thm)], ['183', '184'])).
% 26.87/27.16  thf('186', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.87/27.16         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_2 @ X0 @ X2))),
% 26.87/27.16      inference('sup+', [status(thm)], ['117', '118'])).
% 26.87/27.16  thf('187', plain,
% 26.87/27.16      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.87/27.16         ((zip_tseitin_1 @ X32 @ X33 @ X34 @ X35) | (r1_partfun1 @ X33 @ X32))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_11])).
% 26.87/27.16  thf('188', plain,
% 26.87/27.16      ((~ (zip_tseitin_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1) @ sk_C_1 @ sk_B @ 
% 26.87/27.16           sk_A_1)
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['38', '39'])).
% 26.87/27.16  thf('189', plain,
% 26.87/27.16      (((r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (zip_tseitin_2 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['187', '188'])).
% 26.87/27.16  thf('190', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['186', '189'])).
% 26.87/27.16  thf('191', plain,
% 26.87/27.16      (![X5 : $i, X6 : $i]:
% 26.87/27.16         (((X5) = (k1_xboole_0))
% 26.87/27.16          | ((X6) = (k1_xboole_0))
% 26.87/27.16          | ((k2_zfmisc_1 @ X6 @ X5) != (k1_xboole_0)))),
% 26.87/27.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 26.87/27.16  thf('192', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((k1_xboole_0) != (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | ((sk_B) = (k1_xboole_0))
% 26.87/27.16          | ((X0) = (k1_xboole_0)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['190', '191'])).
% 26.87/27.16  thf('193', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((X0) = (k1_xboole_0))
% 26.87/27.16          | ((sk_B) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('simplify', [status(thm)], ['192'])).
% 26.87/27.16  thf('194', plain, (((sk_B) != (k1_xboole_0))),
% 26.87/27.16      inference('simpl_trail', [status(thm)], ['24', '95'])).
% 26.87/27.16  thf('195', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((X0) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['193', '194'])).
% 26.87/27.16  thf('196', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (((X0) = (k1_xboole_0))
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('simplify_reflect-', [status(thm)], ['193', '194'])).
% 26.87/27.16  thf('197', plain, ((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 26.87/27.16      inference('demod', [status(thm)], ['138', '161'])).
% 26.87/27.16  thf('198', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((r1_partfun1 @ k1_xboole_0 @ X0)
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup+', [status(thm)], ['196', '197'])).
% 26.87/27.16  thf('199', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         ((r1_partfun1 @ X0 @ X1)
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | (r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup+', [status(thm)], ['195', '198'])).
% 26.87/27.16  thf('200', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i]:
% 26.87/27.16         ((r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16          | (r1_partfun1 @ X0 @ X1))),
% 26.87/27.16      inference('simplify', [status(thm)], ['199'])).
% 26.87/27.16  thf('201', plain, ((r1_partfun1 @ sk_C_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('condensation', [status(thm)], ['200'])).
% 26.87/27.16  thf('202', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((r1_partfun1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B))
% 26.87/27.16          | (zip_tseitin_6 @ sk_B @ X0))),
% 26.87/27.16      inference('sup+', [status(thm)], ['185', '201'])).
% 26.87/27.16  thf('203', plain, (![X0 : $i]: (zip_tseitin_6 @ sk_B @ X0)),
% 26.87/27.16      inference('clc', [status(thm)], ['168', '202'])).
% 26.87/27.16  thf('204', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (v1_funct_1 @ X0)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (zip_tseitin_5 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_D_1 @ 
% 26.87/27.16               X0 @ sk_B @ sk_A_1)
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['9', '203'])).
% 26.87/27.16  thf('205', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((zip_tseitin_3 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_B @ sk_A_1)
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (v1_funct_1 @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['4', '204'])).
% 26.87/27.16  thf('206', plain,
% 26.87/27.16      ((~ (v1_funct_1 @ sk_C_1)
% 26.87/27.16        | ~ (r1_partfun1 @ sk_C_1 @ sk_D_1)
% 26.87/27.16        | (zip_tseitin_3 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_B @ 
% 26.87/27.16           sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['3', '205'])).
% 26.87/27.16  thf('207', plain, ((v1_funct_1 @ sk_C_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('208', plain, ((r1_partfun1 @ sk_C_1 @ sk_D_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('209', plain,
% 26.87/27.16      ((zip_tseitin_3 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_B @ 
% 26.87/27.16        sk_A_1)),
% 26.87/27.16      inference('demod', [status(thm)], ['206', '207', '208'])).
% 26.87/27.16  thf('210', plain,
% 26.87/27.16      (![X41 : $i, X42 : $i, X43 : $i]:
% 26.87/27.16         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 26.87/27.16          | ~ (zip_tseitin_3 @ X41 @ X42 @ X43))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_8])).
% 26.87/27.16  thf('211', plain,
% 26.87/27.16      ((m1_subset_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['209', '210'])).
% 26.87/27.16  thf('212', plain,
% 26.87/27.16      (![X59 : $i]:
% 26.87/27.16         (~ (r1_partfun1 @ sk_D_1 @ X59)
% 26.87/27.16          | ~ (r1_partfun1 @ sk_C_1 @ X59)
% 26.87/27.16          | ~ (m1_subset_1 @ X59 @ 
% 26.87/27.16               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (v1_funct_2 @ X59 @ sk_A_1 @ sk_B)
% 26.87/27.16          | ~ (v1_funct_1 @ X59))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('213', plain,
% 26.87/27.16      ((~ (v1_funct_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (v1_funct_2 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1 @ 
% 26.87/27.16             sk_B)
% 26.87/27.16        | ~ (r1_partfun1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | ~ (r1_partfun1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['211', '212'])).
% 26.87/27.16  thf('214', plain,
% 26.87/27.16      ((zip_tseitin_3 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_B @ 
% 26.87/27.16        sk_A_1)),
% 26.87/27.16      inference('demod', [status(thm)], ['206', '207', '208'])).
% 26.87/27.16  thf('215', plain,
% 26.87/27.16      (![X41 : $i, X42 : $i, X43 : $i]:
% 26.87/27.16         ((v1_funct_1 @ X41) | ~ (zip_tseitin_3 @ X41 @ X42 @ X43))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_8])).
% 26.87/27.16  thf('216', plain, ((v1_funct_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['214', '215'])).
% 26.87/27.16  thf('217', plain,
% 26.87/27.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('218', plain,
% 26.87/27.16      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 26.87/27.16         ((zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52)
% 26.87/27.16          | (zip_tseitin_4 @ X48 @ X49 @ X50 @ X52))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.87/27.16  thf('219', plain,
% 26.87/27.16      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 26.87/27.16         ((r1_partfun1 @ X46 @ X44) | ~ (zip_tseitin_4 @ X44 @ X46 @ X47 @ X45))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.87/27.16  thf('220', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.87/27.16         ((zip_tseitin_5 @ X3 @ X2 @ X1 @ X4 @ X0) | (r1_partfun1 @ X2 @ X3))),
% 26.87/27.16      inference('sup-', [status(thm)], ['218', '219'])).
% 26.87/27.16  thf('221', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (v1_funct_1 @ X0)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (zip_tseitin_5 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_D_1 @ 
% 26.87/27.16               X0 @ sk_B @ sk_A_1)
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['9', '203'])).
% 26.87/27.16  thf('222', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((r1_partfun1 @ sk_D_1 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1))
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (v1_funct_1 @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['220', '221'])).
% 26.87/27.16  thf('223', plain,
% 26.87/27.16      ((~ (v1_funct_1 @ sk_C_1)
% 26.87/27.16        | ~ (r1_partfun1 @ sk_C_1 @ sk_D_1)
% 26.87/27.16        | (r1_partfun1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['217', '222'])).
% 26.87/27.16  thf('224', plain, ((v1_funct_1 @ sk_C_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('225', plain, ((r1_partfun1 @ sk_C_1 @ sk_D_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('226', plain,
% 26.87/27.16      ((r1_partfun1 @ sk_D_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['223', '224', '225'])).
% 26.87/27.16  thf('227', plain,
% 26.87/27.16      ((~ (v1_funct_2 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1 @ 
% 26.87/27.16           sk_B)
% 26.87/27.16        | ~ (r1_partfun1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1)))),
% 26.87/27.16      inference('demod', [status(thm)], ['213', '216', '226'])).
% 26.87/27.16  thf('228', plain,
% 26.87/27.16      ((m1_subset_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ 
% 26.87/27.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('sup-', [status(thm)], ['209', '210'])).
% 26.87/27.16  thf(t131_funct_2, axiom,
% 26.87/27.16    (![A:$i,B:$i,C:$i]:
% 26.87/27.16     ( ( ( v1_funct_1 @ C ) & 
% 26.87/27.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.87/27.16       ( ( v1_partfun1 @ C @ A ) =>
% 26.87/27.16         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 26.87/27.16           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 26.87/27.16  thf('229', plain,
% 26.87/27.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 26.87/27.16         (~ (v1_partfun1 @ X23 @ X24)
% 26.87/27.16          | (v1_funct_2 @ X23 @ X24 @ X25)
% 26.87/27.16          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 26.87/27.16          | ~ (v1_funct_1 @ X23))),
% 26.87/27.16      inference('cnf', [status(esa)], [t131_funct_2])).
% 26.87/27.16  thf('230', plain,
% 26.87/27.16      ((~ (v1_funct_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))
% 26.87/27.16        | (v1_funct_2 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1 @ 
% 26.87/27.16           sk_B)
% 26.87/27.16        | ~ (v1_partfun1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['228', '229'])).
% 26.87/27.16  thf('231', plain, ((v1_funct_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['214', '215'])).
% 26.87/27.16  thf('232', plain,
% 26.87/27.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('233', plain,
% 26.87/27.16      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 26.87/27.16         ((zip_tseitin_5 @ X48 @ X49 @ X50 @ X51 @ X52)
% 26.87/27.16          | (zip_tseitin_4 @ X48 @ X49 @ X50 @ X52))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.87/27.16  thf('234', plain,
% 26.87/27.16      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 26.87/27.16         ((v1_partfun1 @ X44 @ X45) | ~ (zip_tseitin_4 @ X44 @ X46 @ X47 @ X45))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.87/27.16  thf('235', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.87/27.16         ((zip_tseitin_5 @ X3 @ X2 @ X1 @ X4 @ X0) | (v1_partfun1 @ X3 @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['233', '234'])).
% 26.87/27.16  thf('236', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (v1_funct_1 @ X0)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (zip_tseitin_5 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_D_1 @ 
% 26.87/27.16               X0 @ sk_B @ sk_A_1)
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['9', '203'])).
% 26.87/27.16  thf('237', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         ((v1_partfun1 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_A_1)
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (v1_funct_1 @ X0))),
% 26.87/27.16      inference('sup-', [status(thm)], ['235', '236'])).
% 26.87/27.16  thf('238', plain,
% 26.87/27.16      ((~ (v1_funct_1 @ sk_C_1)
% 26.87/27.16        | ~ (r1_partfun1 @ sk_C_1 @ sk_D_1)
% 26.87/27.16        | (v1_partfun1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['232', '237'])).
% 26.87/27.16  thf('239', plain, ((v1_funct_1 @ sk_C_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('240', plain, ((r1_partfun1 @ sk_C_1 @ sk_D_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('241', plain,
% 26.87/27.16      ((v1_partfun1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1)),
% 26.87/27.16      inference('demod', [status(thm)], ['238', '239', '240'])).
% 26.87/27.16  thf('242', plain,
% 26.87/27.16      ((v1_funct_2 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ sk_A_1 @ sk_B)),
% 26.87/27.16      inference('demod', [status(thm)], ['230', '231', '241'])).
% 26.87/27.16  thf('243', plain,
% 26.87/27.16      (~ (r1_partfun1 @ sk_C_1 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['227', '242'])).
% 26.87/27.16  thf('244', plain,
% 26.87/27.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.87/27.16         (zip_tseitin_5 @ (sk_E @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A_1) @ X2 @ 
% 26.87/27.16          sk_C_1 @ X1 @ X0)),
% 26.87/27.16      inference('sup-', [status(thm)], ['2', '243'])).
% 26.87/27.16  thf('245', plain,
% 26.87/27.16      (![X0 : $i]:
% 26.87/27.16         (~ (v1_funct_1 @ X0)
% 26.87/27.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16          | ~ (zip_tseitin_5 @ (sk_E @ sk_D_1 @ X0 @ sk_B @ sk_A_1) @ sk_D_1 @ 
% 26.87/27.16               X0 @ sk_B @ sk_A_1)
% 26.87/27.16          | ~ (r1_partfun1 @ X0 @ sk_D_1))),
% 26.87/27.16      inference('demod', [status(thm)], ['9', '203'])).
% 26.87/27.16  thf('246', plain,
% 26.87/27.16      ((~ (r1_partfun1 @ sk_C_1 @ sk_D_1)
% 26.87/27.16        | ~ (m1_subset_1 @ sk_C_1 @ 
% 26.87/27.16             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 26.87/27.16        | ~ (v1_funct_1 @ sk_C_1))),
% 26.87/27.16      inference('sup-', [status(thm)], ['244', '245'])).
% 26.87/27.16  thf('247', plain, ((r1_partfun1 @ sk_C_1 @ sk_D_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('248', plain,
% 26.87/27.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('249', plain, ((v1_funct_1 @ sk_C_1)),
% 26.87/27.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.87/27.16  thf('250', plain, ($false),
% 26.87/27.16      inference('demod', [status(thm)], ['246', '247', '248', '249'])).
% 26.87/27.16  
% 26.87/27.16  % SZS output end Refutation
% 26.87/27.16  
% 26.87/27.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
