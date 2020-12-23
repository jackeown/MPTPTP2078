%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oM75CMVC12

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:12 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  209 (2817 expanded)
%              Number of leaves         :   35 ( 790 expanded)
%              Depth                    :   31
%              Number of atoms          : 2045 (55407 expanded)
%              Number of equality atoms :  175 (4249 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t145_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( A = k1_xboole_0 ) )
           => ( ( r1_partfun1 @ C @ D )
            <=> ! [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( A = k1_xboole_0 ) )
             => ( ( r1_partfun1 @ C @ D )
              <=> ! [E: $i] :
                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                   => ( ( k1_funct_1 @ C @ E )
                      = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('11',plain,
    ( ( v4_relat_1 @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

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

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','34'])).

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

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( r1_partfun1 @ X20 @ X19 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('43',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('46',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X22 )
        = ( k1_funct_1 @ sk_D @ X22 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X22 )
        = ( k1_funct_1 @ sk_D @ X22 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
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

thf('53',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('57',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('60',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('71',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('85',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('89',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','90'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('94',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('96',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( r1_partfun1 @ X20 @ X19 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('105',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('107',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X22 )
        = ( k1_funct_1 @ sk_D @ X22 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X22 )
          = ( k1_funct_1 @ sk_D @ X22 ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X22 )
          = ( k1_funct_1 @ sk_D @ X22 ) ) ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X22 )
          = ( k1_funct_1 @ sk_D @ X22 ) ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
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

thf('112',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('114',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('116',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('119',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118'])).

thf('120',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['62'])).

thf('122',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['62'])).

thf('124',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('125',plain,
    ( ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X22 )
          = ( k1_funct_1 @ sk_D @ X22 ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X22 )
          = ( k1_funct_1 @ sk_D @ X22 ) ) ) ),
    inference(split,[status(esa)],['107'])).

thf('126',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['62'])).

thf('128',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ! [X22: $i] :
          ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X22 )
            = ( k1_funct_1 @ sk_D @ X22 ) ) )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('131',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X22 )
          = ( k1_funct_1 @ sk_D @ X22 ) ) ) ),
    inference(split,[status(esa)],['107'])).

thf('132',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,(
    r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['64','122','123','129','130','131','132'])).

thf('134',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','133'])).

thf('135',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('136',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('137',plain,(
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

thf('138',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('141',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','133'])).

thf('143',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('144',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('145',plain,(
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

thf('146',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('149',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['107'])).

thf('152',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['64','122','123','132','129','130','131'])).

thf('153',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','153','154','155'])).

thf('157',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['142','156'])).

thf('158',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['62'])).

thf('159',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['64','122','132','129','130','131','123'])).

thf('160',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['157','160'])).

thf('162',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('163',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['141','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['135','164'])).

thf('166',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['151','152'])).

thf('167',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['134','169'])).

thf('171',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('172',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['170','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oM75CMVC12
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.18/1.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.41  % Solved by: fo/fo7.sh
% 1.18/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.41  % done 1118 iterations in 0.958s
% 1.18/1.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.41  % SZS output start Refutation
% 1.18/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.41  thf(sk_D_type, type, sk_D: $i).
% 1.18/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.18/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.18/1.41  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.18/1.41  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.18/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.18/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.41  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 1.18/1.41  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.18/1.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.18/1.41  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.18/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.41  thf(sk_E_type, type, sk_E: $i).
% 1.18/1.41  thf(t145_funct_2, conjecture,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( ( v1_funct_1 @ C ) & 
% 1.18/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41       ( ![D:$i]:
% 1.18/1.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.18/1.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.41             ( ( r1_partfun1 @ C @ D ) <=>
% 1.18/1.41               ( ![E:$i]:
% 1.18/1.41                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 1.18/1.41                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 1.18/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.41    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.41        ( ( ( v1_funct_1 @ C ) & 
% 1.18/1.41            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41          ( ![D:$i]:
% 1.18/1.41            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.18/1.41                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.41                ( ( r1_partfun1 @ C @ D ) <=>
% 1.18/1.41                  ( ![E:$i]:
% 1.18/1.41                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 1.18/1.41                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 1.18/1.41    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 1.18/1.41  thf('0', plain,
% 1.18/1.41      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('1', plain,
% 1.18/1.41      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 1.18/1.41         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.18/1.41      inference('split', [status(esa)], ['0'])).
% 1.18/1.41  thf('2', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(redefinition_k1_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.18/1.41  thf('3', plain,
% 1.18/1.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.41         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.18/1.41          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.41  thf('4', plain,
% 1.18/1.41      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.18/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.41  thf('5', plain,
% 1.18/1.41      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1)))
% 1.18/1.41         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.18/1.41      inference('demod', [status(thm)], ['1', '4'])).
% 1.18/1.41  thf('6', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('7', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('split', [status(esa)], ['6'])).
% 1.18/1.41  thf('8', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('9', plain,
% 1.18/1.41      (((m1_subset_1 @ sk_C_1 @ 
% 1.18/1.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup+', [status(thm)], ['7', '8'])).
% 1.18/1.41  thf(cc2_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.18/1.41  thf('10', plain,
% 1.18/1.41      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.18/1.41         ((v4_relat_1 @ X5 @ X6)
% 1.18/1.41          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.18/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.18/1.41  thf('11', plain,
% 1.18/1.41      (((v4_relat_1 @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['9', '10'])).
% 1.18/1.41  thf(d18_relat_1, axiom,
% 1.18/1.41    (![A:$i,B:$i]:
% 1.18/1.41     ( ( v1_relat_1 @ B ) =>
% 1.18/1.41       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.18/1.41  thf('12', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i]:
% 1.18/1.41         (~ (v4_relat_1 @ X0 @ X1)
% 1.18/1.41          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.18/1.41          | ~ (v1_relat_1 @ X0))),
% 1.18/1.41      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.18/1.41  thf('13', plain,
% 1.18/1.41      (((~ (v1_relat_1 @ sk_C_1)
% 1.18/1.41         | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0)))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['11', '12'])).
% 1.18/1.41  thf('14', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(cc1_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( v1_relat_1 @ C ) ))).
% 1.18/1.41  thf('15', plain,
% 1.18/1.41      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.41         ((v1_relat_1 @ X2)
% 1.18/1.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.18/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.18/1.41  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('17', plain,
% 1.18/1.41      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['13', '16'])).
% 1.18/1.41  thf('18', plain,
% 1.18/1.41      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('split', [status(esa)], ['6'])).
% 1.18/1.41  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('20', plain,
% 1.18/1.41      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup+', [status(thm)], ['18', '19'])).
% 1.18/1.41  thf(d1_funct_2, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.41           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.18/1.41             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.18/1.41         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.41           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.18/1.41             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.18/1.41  thf(zf_stmt_1, axiom,
% 1.18/1.41    (![C:$i,B:$i,A:$i]:
% 1.18/1.41     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.18/1.41       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.41  thf('21', plain,
% 1.18/1.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.18/1.41         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.18/1.41          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.18/1.41          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.41  thf('22', plain,
% 1.18/1.41      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.18/1.41         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.41  thf('23', plain,
% 1.18/1.41      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('split', [status(esa)], ['6'])).
% 1.18/1.41  thf('24', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('25', plain,
% 1.18/1.41      (((m1_subset_1 @ sk_D @ 
% 1.18/1.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup+', [status(thm)], ['23', '24'])).
% 1.18/1.41  thf('26', plain,
% 1.18/1.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.41         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.18/1.41          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.41  thf('27', plain,
% 1.18/1.41      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['25', '26'])).
% 1.18/1.41  thf('28', plain,
% 1.18/1.41      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.18/1.41         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['22', '27'])).
% 1.18/1.41  thf('29', plain,
% 1.18/1.41      (((m1_subset_1 @ sk_D @ 
% 1.18/1.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup+', [status(thm)], ['23', '24'])).
% 1.18/1.41  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.18/1.41  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.18/1.41  thf(zf_stmt_4, axiom,
% 1.18/1.41    (![B:$i,A:$i]:
% 1.18/1.41     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.41       ( zip_tseitin_0 @ B @ A ) ))).
% 1.18/1.41  thf(zf_stmt_5, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.18/1.41         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.41           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.18/1.41             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.18/1.41  thf('30', plain,
% 1.18/1.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.41         (~ (zip_tseitin_0 @ X16 @ X17)
% 1.18/1.41          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 1.18/1.41          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.41  thf('31', plain,
% 1.18/1.41      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.18/1.41         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['29', '30'])).
% 1.18/1.41  thf('32', plain,
% 1.18/1.41      (![X11 : $i, X12 : $i]:
% 1.18/1.41         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.18/1.41  thf('33', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 1.18/1.41      inference('simplify', [status(thm)], ['32'])).
% 1.18/1.41  thf('34', plain,
% 1.18/1.41      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['31', '33'])).
% 1.18/1.41  thf('35', plain,
% 1.18/1.41      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['28', '34'])).
% 1.18/1.41  thf(t132_partfun1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.41       ( ![B:$i]:
% 1.18/1.41         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.18/1.41           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.18/1.41             ( ( r1_partfun1 @ A @ B ) <=>
% 1.18/1.41               ( ![C:$i]:
% 1.18/1.41                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.18/1.41                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 1.18/1.41  thf('36', plain,
% 1.18/1.41      (![X19 : $i, X20 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X19)
% 1.18/1.41          | ~ (v1_funct_1 @ X19)
% 1.18/1.41          | (r2_hidden @ (sk_C @ X19 @ X20) @ (k1_relat_1 @ X20))
% 1.18/1.41          | (r1_partfun1 @ X20 @ X19)
% 1.18/1.41          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 1.18/1.41          | ~ (v1_funct_1 @ X20)
% 1.18/1.41          | ~ (v1_relat_1 @ X20))),
% 1.18/1.41      inference('cnf', [status(esa)], [t132_partfun1])).
% 1.18/1.41  thf('37', plain,
% 1.18/1.41      ((![X0 : $i]:
% 1.18/1.41          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 1.18/1.41           | ~ (v1_relat_1 @ X0)
% 1.18/1.41           | ~ (v1_funct_1 @ X0)
% 1.18/1.41           | (r1_partfun1 @ X0 @ sk_D)
% 1.18/1.41           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 1.18/1.41           | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41           | ~ (v1_relat_1 @ sk_D)))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.41  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('39', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('40', plain,
% 1.18/1.41      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.41         ((v1_relat_1 @ X2)
% 1.18/1.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.18/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.18/1.41  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.41  thf('42', plain,
% 1.18/1.41      ((![X0 : $i]:
% 1.18/1.41          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 1.18/1.41           | ~ (v1_relat_1 @ X0)
% 1.18/1.41           | ~ (v1_funct_1 @ X0)
% 1.18/1.41           | (r1_partfun1 @ X0 @ sk_D)
% 1.18/1.41           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['37', '38', '41'])).
% 1.18/1.41  thf('43', plain,
% 1.18/1.41      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.41         | ~ (v1_relat_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['17', '42'])).
% 1.18/1.41  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('46', plain,
% 1.18/1.41      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.18/1.41  thf('47', plain,
% 1.18/1.41      (![X22 : $i]:
% 1.18/1.41         (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41          | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))
% 1.18/1.41          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('48', plain,
% 1.18/1.41      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.18/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.41  thf('49', plain,
% 1.18/1.41      (![X22 : $i]:
% 1.18/1.41         (~ (r2_hidden @ X22 @ (k1_relat_1 @ sk_C_1))
% 1.18/1.41          | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))
% 1.18/1.41          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['47', '48'])).
% 1.18/1.41  thf('50', plain,
% 1.18/1.41      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.41             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['46', '49'])).
% 1.18/1.41  thf('51', plain,
% 1.18/1.41      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.41           = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('simplify', [status(thm)], ['50'])).
% 1.18/1.41  thf('52', plain,
% 1.18/1.41      (![X19 : $i, X20 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X19)
% 1.18/1.41          | ~ (v1_funct_1 @ X19)
% 1.18/1.41          | ((k1_funct_1 @ X20 @ (sk_C @ X19 @ X20))
% 1.18/1.41              != (k1_funct_1 @ X19 @ (sk_C @ X19 @ X20)))
% 1.18/1.41          | (r1_partfun1 @ X20 @ X19)
% 1.18/1.41          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 1.18/1.41          | ~ (v1_funct_1 @ X20)
% 1.18/1.41          | ~ (v1_relat_1 @ X20))),
% 1.18/1.41      inference('cnf', [status(esa)], [t132_partfun1])).
% 1.18/1.41  thf('53', plain,
% 1.18/1.41      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.41           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ~ (v1_relat_1 @ sk_C_1)
% 1.18/1.41         | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.41         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['51', '52'])).
% 1.18/1.41  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('56', plain,
% 1.18/1.41      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['28', '34'])).
% 1.18/1.41  thf('57', plain,
% 1.18/1.41      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 1.18/1.41         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['13', '16'])).
% 1.18/1.41  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.41  thf('60', plain,
% 1.18/1.41      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.41           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)],
% 1.18/1.41                ['53', '54', '55', '56', '57', '58', '59'])).
% 1.18/1.41  thf('61', plain,
% 1.18/1.41      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.41      inference('simplify', [status(thm)], ['60'])).
% 1.18/1.41  thf('62', plain,
% 1.18/1.41      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 1.18/1.41        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('63', plain,
% 1.18/1.41      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 1.18/1.41      inference('split', [status(esa)], ['62'])).
% 1.18/1.41  thf('64', plain,
% 1.18/1.41      (((r1_partfun1 @ sk_C_1 @ sk_D)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.18/1.41      inference('sup-', [status(thm)], ['61', '63'])).
% 1.18/1.41  thf('65', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('66', plain,
% 1.18/1.41      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.18/1.41         ((v4_relat_1 @ X5 @ X6)
% 1.18/1.41          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.18/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.18/1.41  thf('67', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 1.18/1.41      inference('sup-', [status(thm)], ['65', '66'])).
% 1.18/1.41  thf('68', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i]:
% 1.18/1.41         (~ (v4_relat_1 @ X0 @ X1)
% 1.18/1.41          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.18/1.41          | ~ (v1_relat_1 @ X0))),
% 1.18/1.41      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.18/1.41  thf('69', plain,
% 1.18/1.41      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 1.18/1.41      inference('sup-', [status(thm)], ['67', '68'])).
% 1.18/1.41  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('71', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.18/1.41      inference('demod', [status(thm)], ['69', '70'])).
% 1.18/1.41  thf('72', plain,
% 1.18/1.41      (![X11 : $i, X12 : $i]:
% 1.18/1.41         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.18/1.41  thf('73', plain,
% 1.18/1.41      (![X11 : $i, X12 : $i]:
% 1.18/1.41         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.18/1.41  thf('74', plain,
% 1.18/1.41      (![X11 : $i, X12 : $i]:
% 1.18/1.41         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.18/1.41  thf('75', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.18/1.41         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 1.18/1.41      inference('sup+', [status(thm)], ['73', '74'])).
% 1.18/1.41  thf('76', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('77', plain,
% 1.18/1.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.41         (~ (zip_tseitin_0 @ X16 @ X17)
% 1.18/1.41          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 1.18/1.41          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.41  thf('78', plain,
% 1.18/1.41      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.18/1.41      inference('sup-', [status(thm)], ['76', '77'])).
% 1.18/1.41  thf('79', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i]:
% 1.18/1.41         ((zip_tseitin_0 @ X1 @ X0)
% 1.18/1.41          | ((sk_B) = (X1))
% 1.18/1.41          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.18/1.41      inference('sup-', [status(thm)], ['75', '78'])).
% 1.18/1.41  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('81', plain,
% 1.18/1.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.18/1.41         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.18/1.41          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.18/1.41          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.41  thf('82', plain,
% 1.18/1.41      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.18/1.41        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.18/1.41      inference('sup-', [status(thm)], ['80', '81'])).
% 1.18/1.41  thf('83', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('84', plain,
% 1.18/1.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.41         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.18/1.41          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.41  thf('85', plain,
% 1.18/1.41      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.18/1.41      inference('sup-', [status(thm)], ['83', '84'])).
% 1.18/1.41  thf('86', plain,
% 1.18/1.41      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.18/1.41      inference('demod', [status(thm)], ['82', '85'])).
% 1.18/1.41  thf('87', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i]:
% 1.18/1.41         (((sk_B) = (X0))
% 1.18/1.41          | (zip_tseitin_0 @ X0 @ X1)
% 1.18/1.41          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.18/1.41      inference('sup-', [status(thm)], ['79', '86'])).
% 1.18/1.41  thf('88', plain,
% 1.18/1.41      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('split', [status(esa)], ['6'])).
% 1.18/1.41  thf('89', plain,
% 1.18/1.41      ((![X0 : $i, X1 : $i]:
% 1.18/1.41          (((X0) != (k1_xboole_0))
% 1.18/1.41           | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.18/1.41           | (zip_tseitin_0 @ X0 @ X1)))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['87', '88'])).
% 1.18/1.41  thf('90', plain,
% 1.18/1.41      ((![X1 : $i]:
% 1.18/1.41          ((zip_tseitin_0 @ k1_xboole_0 @ X1) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('simplify', [status(thm)], ['89'])).
% 1.18/1.41  thf('91', plain,
% 1.18/1.41      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.41          ((zip_tseitin_0 @ X0 @ X1)
% 1.18/1.41           | (zip_tseitin_0 @ X0 @ X2)
% 1.18/1.41           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup+', [status(thm)], ['72', '90'])).
% 1.18/1.41  thf('92', plain,
% 1.18/1.41      ((![X0 : $i, X1 : $i]:
% 1.18/1.41          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('condensation', [status(thm)], ['91'])).
% 1.18/1.41  thf('93', plain,
% 1.18/1.41      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.18/1.41      inference('sup-', [status(thm)], ['76', '77'])).
% 1.18/1.41  thf('94', plain,
% 1.18/1.41      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['92', '93'])).
% 1.18/1.41  thf('95', plain,
% 1.18/1.41      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.18/1.41      inference('demod', [status(thm)], ['82', '85'])).
% 1.18/1.41  thf('96', plain,
% 1.18/1.41      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('clc', [status(thm)], ['94', '95'])).
% 1.18/1.41  thf('97', plain,
% 1.18/1.41      (![X19 : $i, X20 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X19)
% 1.18/1.41          | ~ (v1_funct_1 @ X19)
% 1.18/1.41          | (r2_hidden @ (sk_C @ X19 @ X20) @ (k1_relat_1 @ X20))
% 1.18/1.41          | (r1_partfun1 @ X20 @ X19)
% 1.18/1.41          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 1.18/1.41          | ~ (v1_funct_1 @ X20)
% 1.18/1.41          | ~ (v1_relat_1 @ X20))),
% 1.18/1.41      inference('cnf', [status(esa)], [t132_partfun1])).
% 1.18/1.41  thf('98', plain,
% 1.18/1.41      ((![X0 : $i]:
% 1.18/1.41          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.18/1.41           | ~ (v1_relat_1 @ X0)
% 1.18/1.41           | ~ (v1_funct_1 @ X0)
% 1.18/1.41           | (r1_partfun1 @ X0 @ sk_D)
% 1.18/1.41           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 1.18/1.41           | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41           | ~ (v1_relat_1 @ sk_D)))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['96', '97'])).
% 1.18/1.41  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.41  thf('101', plain,
% 1.18/1.41      ((![X0 : $i]:
% 1.18/1.41          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.18/1.41           | ~ (v1_relat_1 @ X0)
% 1.18/1.41           | ~ (v1_funct_1 @ X0)
% 1.18/1.41           | (r1_partfun1 @ X0 @ sk_D)
% 1.18/1.41           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.18/1.41  thf('102', plain,
% 1.18/1.41      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.41         | ~ (v1_relat_1 @ sk_C_1))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['71', '101'])).
% 1.18/1.41  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('104', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('105', plain,
% 1.18/1.41      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.18/1.41  thf('106', plain,
% 1.18/1.41      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.18/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.41  thf('107', plain,
% 1.18/1.41      (![X22 : $i]:
% 1.18/1.41         (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41          | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))
% 1.18/1.41          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('108', plain,
% 1.18/1.41      ((![X22 : $i]:
% 1.18/1.41          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41           | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))))
% 1.18/1.41         <= ((![X22 : $i]:
% 1.18/1.41                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.41      inference('split', [status(esa)], ['107'])).
% 1.18/1.41  thf('109', plain,
% 1.18/1.41      ((![X0 : $i]:
% 1.18/1.41          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 1.18/1.41           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 1.18/1.41         <= ((![X22 : $i]:
% 1.18/1.41                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['106', '108'])).
% 1.18/1.41  thf('110', plain,
% 1.18/1.41      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.41             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.18/1.41             (![X22 : $i]:
% 1.18/1.41                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['105', '109'])).
% 1.18/1.41  thf('111', plain,
% 1.18/1.41      (![X19 : $i, X20 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X19)
% 1.18/1.41          | ~ (v1_funct_1 @ X19)
% 1.18/1.41          | ((k1_funct_1 @ X20 @ (sk_C @ X19 @ X20))
% 1.18/1.41              != (k1_funct_1 @ X19 @ (sk_C @ X19 @ X20)))
% 1.18/1.41          | (r1_partfun1 @ X20 @ X19)
% 1.18/1.41          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 1.18/1.41          | ~ (v1_funct_1 @ X20)
% 1.18/1.41          | ~ (v1_relat_1 @ X20))),
% 1.18/1.41      inference('cnf', [status(esa)], [t132_partfun1])).
% 1.18/1.41  thf('112', plain,
% 1.18/1.41      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.41           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ~ (v1_relat_1 @ sk_C_1)
% 1.18/1.41         | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.41         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 1.18/1.41         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.41         | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41         | ~ (v1_relat_1 @ sk_D)))
% 1.18/1.41         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.18/1.41             (![X22 : $i]:
% 1.18/1.41                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.41                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['110', '111'])).
% 1.18/1.41  thf('113', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('114', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('115', plain,
% 1.18/1.41      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.41      inference('clc', [status(thm)], ['94', '95'])).
% 1.18/1.41  thf('116', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.18/1.41      inference('demod', [status(thm)], ['69', '70'])).
% 1.18/1.41  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.41  thf('119', plain,
% 1.18/1.42      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 1.18/1.42           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 1.18/1.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.42         | (r1_partfun1 @ sk_C_1 @ sk_D)))
% 1.18/1.42         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.18/1.42             (![X22 : $i]:
% 1.18/1.42                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.42      inference('demod', [status(thm)],
% 1.18/1.42                ['112', '113', '114', '115', '116', '117', '118'])).
% 1.18/1.42  thf('120', plain,
% 1.18/1.42      (((r1_partfun1 @ sk_C_1 @ sk_D))
% 1.18/1.42         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 1.18/1.42             (![X22 : $i]:
% 1.18/1.42                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.42      inference('simplify', [status(thm)], ['119'])).
% 1.18/1.42  thf('121', plain,
% 1.18/1.42      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 1.18/1.42      inference('split', [status(esa)], ['62'])).
% 1.18/1.42  thf('122', plain,
% 1.18/1.42      ((((sk_B) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 1.18/1.42       ~
% 1.18/1.42       (![X22 : $i]:
% 1.18/1.42          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42           | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['120', '121'])).
% 1.18/1.42  thf('123', plain,
% 1.18/1.42      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 1.18/1.42       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.42      inference('split', [status(esa)], ['62'])).
% 1.18/1.42  thf('124', plain,
% 1.18/1.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 1.18/1.42         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('125', plain,
% 1.18/1.42      ((![X22 : $i]:
% 1.18/1.42          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42           | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))))
% 1.18/1.42         <= ((![X22 : $i]:
% 1.18/1.42                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.42      inference('split', [status(esa)], ['107'])).
% 1.18/1.42  thf('126', plain,
% 1.18/1.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 1.18/1.42         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 1.18/1.42             (![X22 : $i]:
% 1.18/1.42                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['124', '125'])).
% 1.18/1.42  thf('127', plain,
% 1.18/1.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 1.18/1.42         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 1.18/1.42      inference('split', [status(esa)], ['62'])).
% 1.18/1.42  thf('128', plain,
% 1.18/1.42      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 1.18/1.42         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 1.18/1.42             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 1.18/1.42             (![X22 : $i]:
% 1.18/1.42                (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42                 | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['126', '127'])).
% 1.18/1.42  thf('129', plain,
% 1.18/1.42      (~
% 1.18/1.42       (![X22 : $i]:
% 1.18/1.42          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42           | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22)))) | 
% 1.18/1.42       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 1.18/1.42       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['128'])).
% 1.18/1.42  thf('130', plain,
% 1.18/1.42      ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.18/1.42      inference('split', [status(esa)], ['6'])).
% 1.18/1.42  thf('131', plain,
% 1.18/1.42      (((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 1.18/1.42       (![X22 : $i]:
% 1.18/1.42          (~ (r2_hidden @ X22 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 1.18/1.42           | ((k1_funct_1 @ sk_C_1 @ X22) = (k1_funct_1 @ sk_D @ X22))))),
% 1.18/1.42      inference('split', [status(esa)], ['107'])).
% 1.18/1.42  thf('132', plain,
% 1.18/1.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 1.18/1.42       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('133', plain,
% 1.18/1.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.18/1.42      inference('sat_resolution*', [status(thm)],
% 1.18/1.42                ['64', '122', '123', '129', '130', '131', '132'])).
% 1.18/1.42  thf('134', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['5', '133'])).
% 1.18/1.42  thf('135', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.18/1.42      inference('demod', [status(thm)], ['69', '70'])).
% 1.18/1.42  thf('136', plain,
% 1.18/1.42      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.42      inference('clc', [status(thm)], ['94', '95'])).
% 1.18/1.42  thf('137', plain,
% 1.18/1.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.18/1.42         (~ (v1_relat_1 @ X19)
% 1.18/1.42          | ~ (v1_funct_1 @ X19)
% 1.18/1.42          | ~ (r1_partfun1 @ X20 @ X19)
% 1.18/1.42          | ((k1_funct_1 @ X20 @ X21) = (k1_funct_1 @ X19 @ X21))
% 1.18/1.42          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 1.18/1.42          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 1.18/1.42          | ~ (v1_funct_1 @ X20)
% 1.18/1.42          | ~ (v1_relat_1 @ X20))),
% 1.18/1.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 1.18/1.42  thf('138', plain,
% 1.18/1.42      ((![X0 : $i, X1 : $i]:
% 1.18/1.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.18/1.42           | ~ (v1_relat_1 @ X0)
% 1.18/1.42           | ~ (v1_funct_1 @ X0)
% 1.18/1.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.18/1.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 1.18/1.42           | ~ (r1_partfun1 @ X0 @ sk_D)
% 1.18/1.42           | ~ (v1_funct_1 @ sk_D)
% 1.18/1.42           | ~ (v1_relat_1 @ sk_D)))
% 1.18/1.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['136', '137'])).
% 1.18/1.42  thf('139', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.42      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.42  thf('141', plain,
% 1.18/1.42      ((![X0 : $i, X1 : $i]:
% 1.18/1.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.18/1.42           | ~ (v1_relat_1 @ X0)
% 1.18/1.42           | ~ (v1_funct_1 @ X0)
% 1.18/1.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.18/1.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 1.18/1.42           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 1.18/1.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.18/1.42      inference('demod', [status(thm)], ['138', '139', '140'])).
% 1.18/1.42  thf('142', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['5', '133'])).
% 1.18/1.42  thf('143', plain,
% 1.18/1.42      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 1.18/1.42         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('demod', [status(thm)], ['13', '16'])).
% 1.18/1.42  thf('144', plain,
% 1.18/1.42      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('demod', [status(thm)], ['28', '34'])).
% 1.18/1.42  thf('145', plain,
% 1.18/1.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.18/1.42         (~ (v1_relat_1 @ X19)
% 1.18/1.42          | ~ (v1_funct_1 @ X19)
% 1.18/1.42          | ~ (r1_partfun1 @ X20 @ X19)
% 1.18/1.42          | ((k1_funct_1 @ X20 @ X21) = (k1_funct_1 @ X19 @ X21))
% 1.18/1.42          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 1.18/1.42          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 1.18/1.42          | ~ (v1_funct_1 @ X20)
% 1.18/1.42          | ~ (v1_relat_1 @ X20))),
% 1.18/1.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 1.18/1.42  thf('146', plain,
% 1.18/1.42      ((![X0 : $i, X1 : $i]:
% 1.18/1.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 1.18/1.42           | ~ (v1_relat_1 @ X0)
% 1.18/1.42           | ~ (v1_funct_1 @ X0)
% 1.18/1.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.18/1.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 1.18/1.42           | ~ (r1_partfun1 @ X0 @ sk_D)
% 1.18/1.42           | ~ (v1_funct_1 @ sk_D)
% 1.18/1.42           | ~ (v1_relat_1 @ sk_D)))
% 1.18/1.42         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['144', '145'])).
% 1.18/1.42  thf('147', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('148', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.42      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.42  thf('149', plain,
% 1.18/1.42      ((![X0 : $i, X1 : $i]:
% 1.18/1.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 1.18/1.42           | ~ (v1_relat_1 @ X0)
% 1.18/1.42           | ~ (v1_funct_1 @ X0)
% 1.18/1.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.18/1.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 1.18/1.42           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 1.18/1.42         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('demod', [status(thm)], ['146', '147', '148'])).
% 1.18/1.42  thf('150', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.42           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 1.18/1.42           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 1.18/1.42           | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.42           | ~ (v1_relat_1 @ sk_C_1)))
% 1.18/1.42         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['143', '149'])).
% 1.18/1.42  thf('151', plain,
% 1.18/1.42      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= (((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 1.18/1.42      inference('split', [status(esa)], ['107'])).
% 1.18/1.42  thf('152', plain, (((r1_partfun1 @ sk_C_1 @ sk_D))),
% 1.18/1.42      inference('sat_resolution*', [status(thm)],
% 1.18/1.42                ['64', '122', '123', '132', '129', '130', '131'])).
% 1.18/1.42  thf('153', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['151', '152'])).
% 1.18/1.42  thf('154', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('155', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.42      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.42  thf('156', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 1.18/1.42           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))))
% 1.18/1.42         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('demod', [status(thm)], ['150', '153', '154', '155'])).
% 1.18/1.42  thf('157', plain,
% 1.18/1.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 1.18/1.42         <= ((((sk_A) = (k1_xboole_0))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['142', '156'])).
% 1.18/1.42  thf('158', plain,
% 1.18/1.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 1.18/1.42         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 1.18/1.42      inference('split', [status(esa)], ['62'])).
% 1.18/1.42  thf('159', plain,
% 1.18/1.42      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 1.18/1.42      inference('sat_resolution*', [status(thm)],
% 1.18/1.42                ['64', '122', '132', '129', '130', '131', '123'])).
% 1.18/1.42  thf('160', plain,
% 1.18/1.42      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 1.18/1.42  thf('161', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.18/1.42      inference('simplify_reflect-', [status(thm)], ['157', '160'])).
% 1.18/1.42  thf('162', plain,
% 1.18/1.42      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.18/1.42      inference('split', [status(esa)], ['6'])).
% 1.18/1.42  thf('163', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.18/1.42      inference('sat_resolution*', [status(thm)], ['161', '162'])).
% 1.18/1.42  thf('164', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 1.18/1.42          | ~ (v1_relat_1 @ X0)
% 1.18/1.42          | ~ (v1_funct_1 @ X0)
% 1.18/1.42          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 1.18/1.42          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 1.18/1.42          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['141', '163'])).
% 1.18/1.42  thf('165', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 1.18/1.42          | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 1.18/1.42          | ~ (v1_funct_1 @ sk_C_1)
% 1.18/1.42          | ~ (v1_relat_1 @ sk_C_1))),
% 1.18/1.42      inference('sup-', [status(thm)], ['135', '164'])).
% 1.18/1.42  thf('166', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['151', '152'])).
% 1.18/1.42  thf('167', plain, ((v1_funct_1 @ sk_C_1)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('168', plain, ((v1_relat_1 @ sk_C_1)),
% 1.18/1.42      inference('sup-', [status(thm)], ['14', '15'])).
% 1.18/1.42  thf('169', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 1.18/1.42      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 1.18/1.42  thf('170', plain,
% 1.18/1.42      (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))),
% 1.18/1.42      inference('sup-', [status(thm)], ['134', '169'])).
% 1.18/1.42  thf('171', plain,
% 1.18/1.42      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 1.18/1.42      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 1.18/1.42  thf('172', plain, ($false),
% 1.18/1.42      inference('simplify_reflect-', [status(thm)], ['170', '171'])).
% 1.18/1.42  
% 1.18/1.42  % SZS output end Refutation
% 1.18/1.42  
% 1.18/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
