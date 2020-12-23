%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6bo7Nub7lX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:52 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  140 (1417 expanded)
%              Number of leaves         :   45 ( 412 expanded)
%              Depth                    :   20
%              Number of atoms          :  991 (15933 expanded)
%              Number of equality atoms :   28 ( 602 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('0',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 @ X46 @ X47 )
      | ( r2_hidden @ X44 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X15 )
      | ( X17
       != ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( k1_funct_1 @ X15 @ X14 ) ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ X52 )
       != X51 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X52 @ X53 @ X51 ) @ X52 @ X53 @ X51 )
      | ( zip_tseitin_2 @ X52 @ X53 @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('7',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ~ ( v1_funct_1 @ X52 )
      | ( zip_tseitin_2 @ X52 @ X53 @ ( k1_relat_1 @ X52 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X52 @ X53 @ ( k1_relat_1 @ X52 ) ) @ X52 @ X53 @ ( k1_relat_1 @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( zip_tseitin_2 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('12',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X40 @ X37 @ X38 ) @ X40 @ X37 @ X38 )
      | ( X39
       != ( k1_funct_2 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('14',plain,(
    ! [X37: $i,X38: $i,X40: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X40 @ X37 @ X38 ) @ X40 @ X37 @ X38 )
      | ~ ( r2_hidden @ X40 @ ( k1_funct_2 @ X38 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X32 = X30 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X30 )
        = X33 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['15','18'])).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['15','18'])).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_funct_1 @ X30 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X43: $i] :
      ( ( v1_funct_2 @ X43 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('40',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('43',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37','43'])).

thf('45',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['15','18'])).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_partfun1 @ X24 @ X25 )
      | ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['57'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('63',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['57'])).

thf('66',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['61','64','65'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['58','66'])).

thf('68',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['56','67'])).

thf('69',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['44','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('75',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['73','74'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('76',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('80',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['58','66'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('91',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['73','74'])).

thf('92',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['73','74'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6bo7Nub7lX
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:42:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.74/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.91  % Solved by: fo/fo7.sh
% 0.74/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.91  % done 528 iterations in 0.451s
% 0.74/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.91  % SZS output start Refutation
% 0.74/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.74/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.74/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.74/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.91  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.74/0.91  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.74/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.91  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.74/0.91  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.74/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.91  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.74/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.74/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.91  thf(t5_funct_2, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.74/0.91       ( ( ( ![D:$i]:
% 0.74/0.91             ( ( r2_hidden @ D @ A ) =>
% 0.74/0.91               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.74/0.91           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.74/0.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.91           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.74/0.91  thf(zf_stmt_0, axiom,
% 0.74/0.91    (![D:$i,C:$i,B:$i,A:$i]:
% 0.74/0.91     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.74/0.91       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.74/0.91  thf('0', plain,
% 0.74/0.91      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.74/0.91         ((zip_tseitin_1 @ X44 @ X45 @ X46 @ X47) | (r2_hidden @ X44 @ X47))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.91  thf(d4_funct_1, axiom,
% 0.74/0.91    (![A:$i]:
% 0.74/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.91       ( ![B:$i,C:$i]:
% 0.74/0.91         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.74/0.91             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.74/0.91               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.74/0.91           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.74/0.91             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.74/0.91               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.74/0.91  thf('1', plain,
% 0.74/0.91      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.74/0.91         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.74/0.91          | (r2_hidden @ (k4_tarski @ X14 @ X17) @ X15)
% 0.74/0.91          | ((X17) != (k1_funct_1 @ X15 @ X14))
% 0.74/0.91          | ~ (v1_funct_1 @ X15)
% 0.74/0.91          | ~ (v1_relat_1 @ X15))),
% 0.74/0.91      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.74/0.91  thf('2', plain,
% 0.74/0.91      (![X14 : $i, X15 : $i]:
% 0.74/0.91         (~ (v1_relat_1 @ X15)
% 0.74/0.91          | ~ (v1_funct_1 @ X15)
% 0.74/0.91          | (r2_hidden @ (k4_tarski @ X14 @ (k1_funct_1 @ X15 @ X14)) @ X15)
% 0.74/0.91          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X15)))),
% 0.74/0.91      inference('simplify', [status(thm)], ['1'])).
% 0.74/0.91  thf('3', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.91         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ (k1_relat_1 @ X0))
% 0.74/0.91          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.74/0.91          | ~ (v1_funct_1 @ X0)
% 0.74/0.91          | ~ (v1_relat_1 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['0', '2'])).
% 0.74/0.91  thf(d1_xboole_0, axiom,
% 0.74/0.91    (![A:$i]:
% 0.74/0.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.91  thf('4', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.91  thf('5', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.91         (~ (v1_relat_1 @ X0)
% 0.74/0.91          | ~ (v1_funct_1 @ X0)
% 0.74/0.91          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k1_relat_1 @ X0))
% 0.74/0.91          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.91  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.74/0.91  thf(zf_stmt_2, axiom,
% 0.74/0.91    (![C:$i,B:$i,A:$i]:
% 0.74/0.91     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.74/0.91       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.74/0.91  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.74/0.91  thf(zf_stmt_4, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.74/0.91       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.74/0.91           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.74/0.91         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 0.74/0.91  thf('6', plain,
% 0.74/0.91      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.74/0.91         (((k1_relat_1 @ X52) != (X51))
% 0.74/0.91          | ~ (zip_tseitin_1 @ (sk_D_1 @ X52 @ X53 @ X51) @ X52 @ X53 @ X51)
% 0.74/0.91          | (zip_tseitin_2 @ X52 @ X53 @ X51)
% 0.74/0.91          | ~ (v1_funct_1 @ X52)
% 0.74/0.91          | ~ (v1_relat_1 @ X52))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.74/0.91  thf('7', plain,
% 0.74/0.91      (![X52 : $i, X53 : $i]:
% 0.74/0.91         (~ (v1_relat_1 @ X52)
% 0.74/0.91          | ~ (v1_funct_1 @ X52)
% 0.74/0.91          | (zip_tseitin_2 @ X52 @ X53 @ (k1_relat_1 @ X52))
% 0.74/0.91          | ~ (zip_tseitin_1 @ (sk_D_1 @ X52 @ X53 @ (k1_relat_1 @ X52)) @ 
% 0.74/0.91               X52 @ X53 @ (k1_relat_1 @ X52)))),
% 0.74/0.91      inference('simplify', [status(thm)], ['6'])).
% 0.74/0.91  thf('8', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         (~ (v1_xboole_0 @ X0)
% 0.74/0.91          | ~ (v1_funct_1 @ X0)
% 0.74/0.91          | ~ (v1_relat_1 @ X0)
% 0.74/0.91          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.74/0.91          | ~ (v1_funct_1 @ X0)
% 0.74/0.91          | ~ (v1_relat_1 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['5', '7'])).
% 0.74/0.91  thf('9', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         ((zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.74/0.91          | ~ (v1_relat_1 @ X0)
% 0.74/0.91          | ~ (v1_funct_1 @ X0)
% 0.74/0.91          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('simplify', [status(thm)], ['8'])).
% 0.74/0.91  thf('10', plain,
% 0.74/0.91      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.74/0.91         ((v1_funct_2 @ X48 @ X50 @ X49) | ~ (zip_tseitin_2 @ X48 @ X49 @ X50))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.91  thf('11', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         (~ (v1_xboole_0 @ X0)
% 0.74/0.91          | ~ (v1_funct_1 @ X0)
% 0.74/0.91          | ~ (v1_relat_1 @ X0)
% 0.74/0.91          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.74/0.91  thf(t121_funct_2, conjecture,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.74/0.91       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.74/0.91  thf(zf_stmt_5, negated_conjecture,
% 0.74/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.91        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.74/0.91          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.74/0.91    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.74/0.91  thf('12', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.74/0.91  thf(d2_funct_2, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.74/0.91       ( ![D:$i]:
% 0.74/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.74/0.91           ( ?[E:$i]:
% 0.74/0.91             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.74/0.91               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.74/0.91               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.74/0.91  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.74/0.91  thf(zf_stmt_7, axiom,
% 0.74/0.91    (![E:$i,D:$i,B:$i,A:$i]:
% 0.74/0.91     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.74/0.91       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.74/0.91         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.74/0.91         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.74/0.91  thf(zf_stmt_8, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.74/0.91       ( ![D:$i]:
% 0.74/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.74/0.91           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.74/0.91  thf('13', plain,
% 0.74/0.91      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.74/0.91         (~ (r2_hidden @ X40 @ X39)
% 0.74/0.91          | (zip_tseitin_0 @ (sk_E_1 @ X40 @ X37 @ X38) @ X40 @ X37 @ X38)
% 0.74/0.91          | ((X39) != (k1_funct_2 @ X38 @ X37)))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.74/0.91  thf('14', plain,
% 0.74/0.91      (![X37 : $i, X38 : $i, X40 : $i]:
% 0.74/0.91         ((zip_tseitin_0 @ (sk_E_1 @ X40 @ X37 @ X38) @ X40 @ X37 @ X38)
% 0.74/0.91          | ~ (r2_hidden @ X40 @ (k1_funct_2 @ X38 @ X37)))),
% 0.74/0.91      inference('simplify', [status(thm)], ['13'])).
% 0.74/0.91  thf('15', plain,
% 0.74/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A) @ sk_C_1 @ sk_B_1 @ 
% 0.74/0.91        sk_A)),
% 0.74/0.91      inference('sup-', [status(thm)], ['12', '14'])).
% 0.74/0.91  thf('16', plain,
% 0.74/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A) @ sk_C_1 @ sk_B_1 @ 
% 0.74/0.91        sk_A)),
% 0.74/0.91      inference('sup-', [status(thm)], ['12', '14'])).
% 0.74/0.91  thf('17', plain,
% 0.74/0.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.91         (((X32) = (X30)) | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.74/0.91  thf('18', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 0.74/0.91      inference('sup-', [status(thm)], ['16', '17'])).
% 0.74/0.91  thf('19', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.74/0.91      inference('demod', [status(thm)], ['15', '18'])).
% 0.74/0.91  thf('20', plain,
% 0.74/0.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.91         (((k1_relat_1 @ X30) = (X33))
% 0.74/0.91          | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.74/0.91  thf('21', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.74/0.91      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.91  thf(d10_xboole_0, axiom,
% 0.74/0.91    (![A:$i,B:$i]:
% 0.74/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.91  thf('22', plain,
% 0.74/0.91      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.74/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.91  thf('23', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.74/0.91      inference('simplify', [status(thm)], ['22'])).
% 0.74/0.91  thf('24', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.74/0.91      inference('simplify', [status(thm)], ['22'])).
% 0.74/0.91  thf(t11_relset_1, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( v1_relat_1 @ C ) =>
% 0.74/0.91       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.74/0.91           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.74/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.74/0.91  thf('25', plain,
% 0.74/0.91      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.91         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.74/0.91          | ~ (r1_tarski @ (k2_relat_1 @ X21) @ X23)
% 0.74/0.91          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.74/0.91          | ~ (v1_relat_1 @ X21))),
% 0.74/0.91      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.74/0.91  thf('26', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         (~ (v1_relat_1 @ X0)
% 0.74/0.91          | (m1_subset_1 @ X0 @ 
% 0.74/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.74/0.91          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.74/0.91  thf('27', plain,
% 0.74/0.91      (![X0 : $i]:
% 0.74/0.91         ((m1_subset_1 @ X0 @ 
% 0.74/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.74/0.91          | ~ (v1_relat_1 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['23', '26'])).
% 0.74/0.91  thf('28', plain,
% 0.74/0.91      (((m1_subset_1 @ sk_C_1 @ 
% 0.74/0.91         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.74/0.91        | ~ (v1_relat_1 @ sk_C_1))),
% 0.74/0.91      inference('sup+', [status(thm)], ['21', '27'])).
% 0.74/0.91  thf('29', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.74/0.91      inference('demod', [status(thm)], ['15', '18'])).
% 0.74/0.91  thf('30', plain,
% 0.74/0.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.91         ((v1_relat_1 @ X30) | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.74/0.91  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.91  thf('32', plain,
% 0.74/0.91      ((m1_subset_1 @ sk_C_1 @ 
% 0.74/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.74/0.91      inference('demod', [status(thm)], ['28', '31'])).
% 0.74/0.91  thf(cc5_funct_2, axiom,
% 0.74/0.91    (![A:$i,B:$i]:
% 0.74/0.91     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.74/0.91       ( ![C:$i]:
% 0.74/0.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.91           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.74/0.91             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.74/0.91  thf('33', plain,
% 0.74/0.91      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.74/0.91         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.74/0.91          | (v1_partfun1 @ X27 @ X28)
% 0.74/0.91          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.74/0.91          | ~ (v1_funct_1 @ X27)
% 0.74/0.91          | (v1_xboole_0 @ X29))),
% 0.74/0.91      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.74/0.91  thf('34', plain,
% 0.74/0.91      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.74/0.91        | ~ (v1_funct_1 @ sk_C_1)
% 0.74/0.91        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.74/0.91        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.74/0.91      inference('sup-', [status(thm)], ['32', '33'])).
% 0.74/0.91  thf('35', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.74/0.91      inference('demod', [status(thm)], ['15', '18'])).
% 0.74/0.91  thf('36', plain,
% 0.74/0.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.91         ((v1_funct_1 @ X30) | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.74/0.91  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.91  thf('38', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.74/0.91      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.91  thf(t3_funct_2, axiom,
% 0.74/0.91    (![A:$i]:
% 0.74/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.91       ( ( v1_funct_1 @ A ) & 
% 0.74/0.91         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.74/0.91         ( m1_subset_1 @
% 0.74/0.91           A @ 
% 0.74/0.91           ( k1_zfmisc_1 @
% 0.74/0.91             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.74/0.91  thf('39', plain,
% 0.74/0.91      (![X43 : $i]:
% 0.74/0.91         ((v1_funct_2 @ X43 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))
% 0.74/0.91          | ~ (v1_funct_1 @ X43)
% 0.74/0.91          | ~ (v1_relat_1 @ X43))),
% 0.74/0.91      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.74/0.91  thf('40', plain,
% 0.74/0.91      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.74/0.91        | ~ (v1_relat_1 @ sk_C_1)
% 0.74/0.91        | ~ (v1_funct_1 @ sk_C_1))),
% 0.74/0.91      inference('sup+', [status(thm)], ['38', '39'])).
% 0.74/0.91  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.91  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.91  thf('43', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.74/0.91      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.74/0.91  thf('44', plain,
% 0.74/0.91      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.74/0.91      inference('demod', [status(thm)], ['34', '37', '43'])).
% 0.74/0.91  thf('45', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.74/0.91      inference('demod', [status(thm)], ['15', '18'])).
% 0.74/0.91  thf('46', plain,
% 0.74/0.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.91         ((r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.74/0.91          | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.74/0.91  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/0.91  thf('48', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         (~ (v1_relat_1 @ X0)
% 0.74/0.91          | (m1_subset_1 @ X0 @ 
% 0.74/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.74/0.91          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.74/0.91  thf('49', plain,
% 0.74/0.91      (((m1_subset_1 @ sk_C_1 @ 
% 0.74/0.91         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))
% 0.74/0.91        | ~ (v1_relat_1 @ sk_C_1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['47', '48'])).
% 0.74/0.91  thf('50', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.74/0.91      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.91  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.91  thf('52', plain,
% 0.74/0.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.74/0.91      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.74/0.91  thf(cc1_funct_2, axiom,
% 0.74/0.91    (![A:$i,B:$i,C:$i]:
% 0.74/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.91       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.74/0.91         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.74/0.91  thf('53', plain,
% 0.74/0.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.74/0.91         (~ (v1_funct_1 @ X24)
% 0.74/0.91          | ~ (v1_partfun1 @ X24 @ X25)
% 0.74/0.91          | (v1_funct_2 @ X24 @ X25 @ X26)
% 0.74/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.74/0.91      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.74/0.91  thf('54', plain,
% 0.74/0.91      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.74/0.91        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.74/0.91        | ~ (v1_funct_1 @ sk_C_1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['52', '53'])).
% 0.74/0.91  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.91  thf('56', plain,
% 0.74/0.91      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.74/0.91      inference('demod', [status(thm)], ['54', '55'])).
% 0.74/0.91  thf('57', plain,
% 0.74/0.91      ((~ (v1_funct_1 @ sk_C_1)
% 0.74/0.91        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.74/0.91        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.74/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.74/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.74/0.91  thf('58', plain,
% 0.74/0.91      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.74/0.91         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.74/0.91      inference('split', [status(esa)], ['57'])).
% 0.74/0.91  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.91  thf('60', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.74/0.91      inference('split', [status(esa)], ['57'])).
% 0.74/0.91  thf('61', plain, (((v1_funct_1 @ sk_C_1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['59', '60'])).
% 0.74/0.91  thf('62', plain,
% 0.74/0.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.74/0.91      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.74/0.91  thf('63', plain,
% 0.74/0.91      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.74/0.91         <= (~
% 0.74/0.91             ((m1_subset_1 @ sk_C_1 @ 
% 0.74/0.91               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 0.74/0.91      inference('split', [status(esa)], ['57'])).
% 0.74/0.91  thf('64', plain,
% 0.74/0.91      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.74/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.74/0.91  thf('65', plain,
% 0.74/0.91      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 0.74/0.91       ~
% 0.74/0.91       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 0.74/0.91       ~ ((v1_funct_1 @ sk_C_1))),
% 0.74/0.91      inference('split', [status(esa)], ['57'])).
% 0.74/0.91  thf('66', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.74/0.91      inference('sat_resolution*', [status(thm)], ['61', '64', '65'])).
% 0.74/0.91  thf('67', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.74/0.91      inference('simpl_trail', [status(thm)], ['58', '66'])).
% 0.74/0.91  thf('68', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.74/0.91      inference('clc', [status(thm)], ['56', '67'])).
% 0.74/0.91  thf('69', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.74/0.91      inference('clc', [status(thm)], ['44', '68'])).
% 0.74/0.91  thf('70', plain,
% 0.74/0.91      (![X0 : $i]:
% 0.74/0.91         ((m1_subset_1 @ X0 @ 
% 0.74/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.74/0.91          | ~ (v1_relat_1 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['23', '26'])).
% 0.74/0.91  thf(cc4_relset_1, axiom,
% 0.74/0.91    (![A:$i,B:$i]:
% 0.74/0.91     ( ( v1_xboole_0 @ A ) =>
% 0.74/0.91       ( ![C:$i]:
% 0.74/0.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.74/0.91           ( v1_xboole_0 @ C ) ) ) ))).
% 0.74/0.91  thf('71', plain,
% 0.74/0.91      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.74/0.91         (~ (v1_xboole_0 @ X18)
% 0.74/0.91          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.74/0.91          | (v1_xboole_0 @ X19))),
% 0.74/0.91      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.74/0.91  thf('72', plain,
% 0.74/0.91      (![X0 : $i]:
% 0.74/0.91         (~ (v1_relat_1 @ X0)
% 0.74/0.91          | (v1_xboole_0 @ X0)
% 0.74/0.91          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.74/0.91      inference('sup-', [status(thm)], ['70', '71'])).
% 0.74/0.91  thf('73', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_relat_1 @ sk_C_1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['69', '72'])).
% 0.74/0.91  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.91  thf('75', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.74/0.91      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/0.91  thf(d3_tarski, axiom,
% 0.74/0.91    (![A:$i,B:$i]:
% 0.74/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.74/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.74/0.91  thf('76', plain,
% 0.74/0.91      (![X4 : $i, X6 : $i]:
% 0.74/0.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.74/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.91  thf('77', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.91  thf('78', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['76', '77'])).
% 0.74/0.91  thf('79', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['76', '77'])).
% 0.74/0.91  thf('80', plain,
% 0.74/0.91      (![X7 : $i, X9 : $i]:
% 0.74/0.91         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.74/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.91  thf('81', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.74/0.91      inference('sup-', [status(thm)], ['79', '80'])).
% 0.74/0.91  thf('82', plain,
% 0.74/0.91      (![X0 : $i, X1 : $i]:
% 0.74/0.91         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['78', '81'])).
% 0.74/0.91  thf('83', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_C_1) = (X0)))),
% 0.74/0.91      inference('sup-', [status(thm)], ['75', '82'])).
% 0.74/0.91  thf('84', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.74/0.91      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.91  thf('85', plain,
% 0.74/0.91      (![X0 : $i]: (((k1_relat_1 @ X0) = (sk_A)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('sup+', [status(thm)], ['83', '84'])).
% 0.74/0.91  thf('86', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.74/0.91      inference('simpl_trail', [status(thm)], ['58', '66'])).
% 0.74/0.91  thf('87', plain,
% 0.74/0.91      (![X0 : $i]:
% 0.74/0.91         (~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ X0) @ sk_B_1)
% 0.74/0.91          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.91      inference('sup-', [status(thm)], ['85', '86'])).
% 0.74/0.91  thf('88', plain,
% 0.74/0.91      ((~ (v1_relat_1 @ sk_C_1)
% 0.74/0.91        | ~ (v1_funct_1 @ sk_C_1)
% 0.74/0.91        | ~ (v1_xboole_0 @ sk_C_1)
% 0.74/0.91        | ~ (v1_xboole_0 @ sk_C_1))),
% 0.74/0.91      inference('sup-', [status(thm)], ['11', '87'])).
% 0.74/0.91  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.91  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 0.74/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.91  thf('91', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.74/0.91      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/0.91  thf('92', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.74/0.91      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/0.91  thf('93', plain, ($false),
% 0.74/0.91      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.74/0.91  
% 0.74/0.91  % SZS output end Refutation
% 0.74/0.91  
% 0.74/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
