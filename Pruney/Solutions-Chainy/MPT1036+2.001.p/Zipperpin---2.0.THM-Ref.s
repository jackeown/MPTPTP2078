%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vjST9q31LI

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:14 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 589 expanded)
%              Number of leaves         :   34 ( 187 expanded)
%              Depth                    :   20
%              Number of atoms          : 1028 (9753 expanded)
%              Number of equality atoms :   55 ( 364 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t146_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
               => ( ( k1_funct_1 @ B @ D )
                  = ( k1_funct_1 @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X22 )
        = ( k1_funct_1 @ sk_C_1 @ X22 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('25',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','28','31'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( r1_partfun1 @ X20 @ X19 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,
    ( ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C_1 @ X0 ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C @ X19 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_C @ X19 @ X20 ) ) )
      | ( r1_partfun1 @ X20 @ X19 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('49',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','28','31'])).

thf('53',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('56',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54','55'])).

thf('57',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X22 )
          = ( k1_funct_1 @ sk_C_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ~ ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X22 )
            = ( k1_funct_1 @ sk_C_1 @ X22 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,(
    r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','60','61'])).

thf('63',plain,(
    r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['5','62'])).

thf('64',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','28','31'])).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r1_partfun1 @ X20 @ X19 )
      | ( ( k1_funct_1 @ X20 @ X21 )
        = ( k1_funct_1 @ X19 @ X21 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('73',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['7','60'])).

thf('74',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','74','75','76'])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_B @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['58'])).

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('81',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['7','60','80'])).

thf('82',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vjST9q31LI
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 135 iterations in 0.087s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(t146_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ B ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.54       ( ![C:$i]:
% 0.35/0.54         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.35/0.54             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.54           ( ( r1_partfun1 @ B @ C ) <=>
% 0.35/0.54             ( ![D:$i]:
% 0.35/0.54               ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.35/0.54                 ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i]:
% 0.35/0.54        ( ( ( v1_funct_1 @ B ) & 
% 0.35/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.54          ( ![C:$i]:
% 0.35/0.54            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.35/0.54                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.54              ( ( r1_partfun1 @ B @ C ) <=>
% 0.35/0.54                ( ![D:$i]:
% 0.35/0.54                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.35/0.54                    ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t146_funct_2])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))
% 0.35/0.54         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B)))
% 0.35/0.54         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.35/0.54      inference('demod', [status(thm)], ['1', '4'])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X22 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54          | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22))
% 0.35/0.54          | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (((r1_partfun1 @ sk_B @ sk_C_1)) | 
% 0.35/0.54       (![X22 : $i]:
% 0.35/0.54          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54           | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22))))),
% 0.35/0.54      inference('split', [status(esa)], ['6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.54         ((v4_relat_1 @ X5 @ X6)
% 0.35/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('10', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf(d18_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (v4_relat_1 @ X0 @ X1)
% 0.35/0.54          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.35/0.54          | ~ (v1_relat_1 @ X0))),
% 0.35/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( v1_relat_1 @ C ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X2)
% 0.35/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '15'])).
% 0.35/0.54  thf('17', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d1_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.35/0.54          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.35/0.54          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.35/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C_1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_4, axiom,
% 0.35/0.54    (![B:$i,A:$i]:
% 0.35/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.54  thf(zf_stmt_5, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.35/0.54          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.35/0.54        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.54  thf('25', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 0.35/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.35/0.54      inference('sup+', [status(thm)], ['23', '25'])).
% 0.35/0.54  thf('27', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.35/0.54      inference('eq_fact', [status(thm)], ['26'])).
% 0.35/0.54  thf('28', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '28', '31'])).
% 0.35/0.54  thf(t132_partfun1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.54           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.54             ( ( r1_partfun1 @ A @ B ) <=>
% 0.35/0.54               ( ![C:$i]:
% 0.35/0.54                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.54                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X19)
% 0.35/0.54          | ~ (v1_funct_1 @ X19)
% 0.35/0.54          | (r2_hidden @ (sk_C @ X19 @ X20) @ (k1_relat_1 @ X20))
% 0.35/0.54          | (r1_partfun1 @ X20 @ X19)
% 0.35/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | ~ (v1_relat_1 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.35/0.54          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0))
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain, ((v1_funct_1 @ sk_C_1)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X2)
% 0.35/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.35/0.54          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '35', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.35/0.54        | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.35/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.35/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '39'])).
% 0.35/0.54  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.35/0.54        | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      ((![X22 : $i]:
% 0.35/0.54          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54           | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22))))
% 0.35/0.54         <= ((![X22 : $i]:
% 0.35/0.54                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54                 | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))))),
% 0.35/0.54      inference('split', [status(esa)], ['6'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      ((![X0 : $i]:
% 0.35/0.54          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.35/0.54           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))))
% 0.35/0.54         <= ((![X22 : $i]:
% 0.35/0.54                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54                 | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      ((((r1_partfun1 @ sk_B @ sk_C_1)
% 0.35/0.54         | ((k1_funct_1 @ sk_B @ (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54             = (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))))
% 0.35/0.54         <= ((![X22 : $i]:
% 0.35/0.54                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54                 | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['43', '46'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X19)
% 0.35/0.54          | ~ (v1_funct_1 @ X19)
% 0.35/0.54          | ((k1_funct_1 @ X20 @ (sk_C @ X19 @ X20))
% 0.35/0.54              != (k1_funct_1 @ X19 @ (sk_C @ X19 @ X20)))
% 0.35/0.54          | (r1_partfun1 @ X20 @ X19)
% 0.35/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | ~ (v1_relat_1 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.35/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.35/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.35/0.54         | ~ (v1_funct_1 @ sk_B)
% 0.35/0.54         | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C_1))
% 0.35/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.35/0.54         | ~ (v1_funct_1 @ sk_C_1)
% 0.35/0.54         | ~ (v1_relat_1 @ sk_C_1)))
% 0.35/0.54         <= ((![X22 : $i]:
% 0.35/0.54                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54                 | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.35/0.54  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('52', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '28', '31'])).
% 0.35/0.54  thf('53', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '15'])).
% 0.35/0.54  thf('54', plain, ((v1_funct_1 @ sk_C_1)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.35/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.35/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)))
% 0.35/0.54         <= ((![X22 : $i]:
% 0.35/0.54                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54                 | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))))),
% 0.35/0.54      inference('demod', [status(thm)],
% 0.35/0.54                ['49', '50', '51', '52', '53', '54', '55'])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (((r1_partfun1 @ sk_B @ sk_C_1))
% 0.35/0.54         <= ((![X22 : $i]:
% 0.35/0.54                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54                 | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))
% 0.35/0.54        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      ((~ (r1_partfun1 @ sk_B @ sk_C_1)) <= (~ ((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.35/0.54      inference('split', [status(esa)], ['58'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (~
% 0.35/0.54       (![X22 : $i]:
% 0.35/0.54          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.35/0.54           | ((k1_funct_1 @ sk_B @ X22) = (k1_funct_1 @ sk_C_1 @ X22)))) | 
% 0.35/0.54       ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['57', '59'])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.35/0.54       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('62', plain, (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['7', '60', '61'])).
% 0.35/0.54  thf('63', plain, ((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['5', '62'])).
% 0.35/0.54  thf('64', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '15'])).
% 0.35/0.54  thf('65', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '28', '31'])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X19)
% 0.35/0.54          | ~ (v1_funct_1 @ X19)
% 0.35/0.54          | ~ (r1_partfun1 @ X20 @ X19)
% 0.35/0.54          | ((k1_funct_1 @ X20 @ X21) = (k1_funct_1 @ X19 @ X21))
% 0.35/0.54          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.35/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | ~ (v1_relat_1 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.35/0.54          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.35/0.54          | ~ (r1_partfun1 @ X0 @ sk_C_1)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.54  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.35/0.54          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.35/0.54          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r1_partfun1 @ sk_B @ sk_C_1)
% 0.35/0.54          | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.35/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['64', '70'])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      (((r1_partfun1 @ sk_B @ sk_C_1)) <= (((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.35/0.54      inference('split', [status(esa)], ['6'])).
% 0.35/0.54  thf('73', plain, (((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['7', '60'])).
% 0.35/0.54  thf('74', plain, ((r1_partfun1 @ sk_B @ sk_C_1)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 0.35/0.54  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('77', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['71', '74', '75', '76'])).
% 0.35/0.54  thf('78', plain,
% 0.35/0.54      (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['63', '77'])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D)))
% 0.35/0.54         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))))),
% 0.35/0.54      inference('split', [status(esa)], ['58'])).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))) | 
% 0.35/0.54       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.35/0.54      inference('split', [status(esa)], ['58'])).
% 0.35/0.54  thf('81', plain,
% 0.35/0.54      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['7', '60', '80'])).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      (((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 0.35/0.54  thf('83', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['78', '82'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
