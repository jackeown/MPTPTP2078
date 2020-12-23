%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eOyhNV9hFT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:13 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  209 (2880 expanded)
%              Number of leaves         :   33 ( 801 expanded)
%              Depth                    :   31
%              Number of atoms          : 2091 (57331 expanded)
%              Number of equality atoms :  178 (4457 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,
    ( ( r1_tarski @ ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X23 )
        = ( k1_funct_1 @ sk_D @ X23 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X23 )
        = ( k1_funct_1 @ sk_D @ X23 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C @ X20 @ X21 ) ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('55',plain,
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('59',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('62',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60','61'])).

thf('63',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('69',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('73',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('83',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','92'])).

thf('94',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['93'])).

thf('95',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('96',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('98',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('107',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('109',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X23 )
        = ( k1_funct_1 @ sk_D @ X23 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X23 )
          = ( k1_funct_1 @ sk_D @ X23 ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X23 )
          = ( k1_funct_1 @ sk_D @ X23 ) ) ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X23 )
          = ( k1_funct_1 @ sk_D @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','111'])).

thf('113',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C @ X20 @ X21 ) ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('114',plain,
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
      & ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('116',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('118',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('119',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('121',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120'])).

thf('122',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('124',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('126',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('127',plain,
    ( ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X23 )
          = ( k1_funct_1 @ sk_D @ X23 ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X23 )
          = ( k1_funct_1 @ sk_D @ X23 ) ) ) ),
    inference(split,[status(esa)],['109'])).

thf('128',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['64'])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X23 )
            = ( k1_funct_1 @ sk_D @ X23 ) ) )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('133',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X23 )
          = ( k1_funct_1 @ sk_D @ X23 ) ) ) ),
    inference(split,[status(esa)],['109'])).

thf('134',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,(
    r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['66','124','125','131','132','133','134'])).

thf('136',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','135'])).

thf('137',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('138',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('139',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r1_partfun1 @ X21 @ X20 )
      | ( ( k1_funct_1 @ X21 @ X22 )
        = ( k1_funct_1 @ X20 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('140',plain,
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
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('143',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','135'])).

thf('145',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('146',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('147',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r1_partfun1 @ X21 @ X20 )
      | ( ( k1_funct_1 @ X21 @ X22 )
        = ( k1_funct_1 @ X20 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('148',plain,
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
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('151',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['109'])).

thf('154',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['66','124','125','134','131','132','133'])).

thf('155',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','155','156','157'])).

thf('159',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','158'])).

thf('160',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['64'])).

thf('161',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['66','124','134','131','132','133','125'])).

thf('162',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['160','161'])).

thf('163',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['159','162'])).

thf('164',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('165',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['143','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['137','166'])).

thf('168',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('169',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['136','171'])).

thf('173',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['160','161'])).

thf('174',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['172','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eOyhNV9hFT
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.19/2.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.19/2.42  % Solved by: fo/fo7.sh
% 2.19/2.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.19/2.42  % done 1267 iterations in 1.962s
% 2.19/2.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.19/2.42  % SZS output start Refutation
% 2.19/2.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.19/2.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.19/2.42  thf(sk_A_type, type, sk_A: $i).
% 2.19/2.42  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.19/2.42  thf(sk_E_type, type, sk_E: $i).
% 2.19/2.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.19/2.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.19/2.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.19/2.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.19/2.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.19/2.42  thf(sk_B_type, type, sk_B: $i).
% 2.19/2.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.19/2.42  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 2.19/2.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.19/2.42  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.19/2.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.19/2.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.19/2.42  thf(sk_D_type, type, sk_D: $i).
% 2.19/2.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.19/2.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.19/2.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.19/2.42  thf(t145_funct_2, conjecture,
% 2.19/2.42    (![A:$i,B:$i,C:$i]:
% 2.19/2.42     ( ( ( v1_funct_1 @ C ) & 
% 2.19/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.19/2.42       ( ![D:$i]:
% 2.19/2.42         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.19/2.42             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.19/2.42           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.19/2.42             ( ( r1_partfun1 @ C @ D ) <=>
% 2.19/2.42               ( ![E:$i]:
% 2.19/2.42                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 2.19/2.42                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 2.19/2.42  thf(zf_stmt_0, negated_conjecture,
% 2.19/2.42    (~( ![A:$i,B:$i,C:$i]:
% 2.19/2.42        ( ( ( v1_funct_1 @ C ) & 
% 2.19/2.42            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.19/2.42          ( ![D:$i]:
% 2.19/2.42            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.19/2.42                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.19/2.42              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.19/2.42                ( ( r1_partfun1 @ C @ D ) <=>
% 2.19/2.42                  ( ![E:$i]:
% 2.19/2.42                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 2.19/2.42                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 2.19/2.42    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 2.19/2.42  thf('0', plain,
% 2.19/2.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('1', plain,
% 2.19/2.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.19/2.42         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.19/2.42      inference('split', [status(esa)], ['0'])).
% 2.19/2.42  thf('2', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf(redefinition_k1_relset_1, axiom,
% 2.19/2.42    (![A:$i,B:$i,C:$i]:
% 2.19/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.19/2.42       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.19/2.42  thf('3', plain,
% 2.19/2.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.19/2.42         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.19/2.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.19/2.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.19/2.42  thf('4', plain,
% 2.19/2.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('sup-', [status(thm)], ['2', '3'])).
% 2.19/2.42  thf('5', plain,
% 2.19/2.42      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1)))
% 2.19/2.42         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.19/2.42      inference('demod', [status(thm)], ['1', '4'])).
% 2.19/2.42  thf('6', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('7', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('split', [status(esa)], ['6'])).
% 2.19/2.42  thf('8', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('9', plain,
% 2.19/2.42      (((m1_subset_1 @ sk_C_1 @ 
% 2.19/2.42         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup+', [status(thm)], ['7', '8'])).
% 2.19/2.42  thf(dt_k1_relset_1, axiom,
% 2.19/2.42    (![A:$i,B:$i,C:$i]:
% 2.19/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.19/2.42       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.19/2.42  thf('10', plain,
% 2.19/2.42      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.19/2.42         ((m1_subset_1 @ (k1_relset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 2.19/2.42          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 2.19/2.42      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 2.19/2.42  thf('11', plain,
% 2.19/2.42      (((m1_subset_1 @ (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1) @ 
% 2.19/2.42         (k1_zfmisc_1 @ k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['9', '10'])).
% 2.19/2.42  thf(t3_subset, axiom,
% 2.19/2.42    (![A:$i,B:$i]:
% 2.19/2.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.19/2.42  thf('12', plain,
% 2.19/2.42      (![X0 : $i, X1 : $i]:
% 2.19/2.42         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 2.19/2.42      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.42  thf('13', plain,
% 2.19/2.42      (((r1_tarski @ (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1) @ k1_xboole_0))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['11', '12'])).
% 2.19/2.42  thf('14', plain,
% 2.19/2.42      (((m1_subset_1 @ sk_C_1 @ 
% 2.19/2.42         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup+', [status(thm)], ['7', '8'])).
% 2.19/2.42  thf('15', plain,
% 2.19/2.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.19/2.42         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.19/2.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.19/2.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.19/2.42  thf('16', plain,
% 2.19/2.42      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['14', '15'])).
% 2.19/2.42  thf('17', plain,
% 2.19/2.42      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['13', '16'])).
% 2.19/2.42  thf('18', plain,
% 2.19/2.42      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('split', [status(esa)], ['6'])).
% 2.19/2.42  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('20', plain,
% 2.19/2.42      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.19/2.42  thf(d1_funct_2, axiom,
% 2.19/2.42    (![A:$i,B:$i,C:$i]:
% 2.19/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.19/2.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.19/2.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.19/2.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.19/2.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.19/2.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.19/2.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.19/2.42  thf(zf_stmt_1, axiom,
% 2.19/2.42    (![C:$i,B:$i,A:$i]:
% 2.19/2.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.19/2.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.19/2.42  thf('21', plain,
% 2.19/2.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.19/2.42         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 2.19/2.42          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.19/2.42          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.19/2.42  thf('22', plain,
% 2.19/2.42      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.19/2.42         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['20', '21'])).
% 2.19/2.42  thf('23', plain,
% 2.19/2.42      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('split', [status(esa)], ['6'])).
% 2.19/2.42  thf('24', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('25', plain,
% 2.19/2.42      (((m1_subset_1 @ sk_D @ 
% 2.19/2.42         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup+', [status(thm)], ['23', '24'])).
% 2.19/2.42  thf('26', plain,
% 2.19/2.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.19/2.42         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.19/2.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.19/2.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.19/2.42  thf('27', plain,
% 2.19/2.42      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['25', '26'])).
% 2.19/2.42  thf('28', plain,
% 2.19/2.42      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.19/2.42         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['22', '27'])).
% 2.19/2.42  thf('29', plain,
% 2.19/2.42      (((m1_subset_1 @ sk_D @ 
% 2.19/2.42         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup+', [status(thm)], ['23', '24'])).
% 2.19/2.42  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.19/2.42  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.19/2.42  thf(zf_stmt_4, axiom,
% 2.19/2.42    (![B:$i,A:$i]:
% 2.19/2.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.19/2.42       ( zip_tseitin_0 @ B @ A ) ))).
% 2.19/2.42  thf(zf_stmt_5, axiom,
% 2.19/2.42    (![A:$i,B:$i,C:$i]:
% 2.19/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.19/2.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.19/2.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.19/2.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.19/2.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.19/2.42  thf('30', plain,
% 2.19/2.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.19/2.42         (~ (zip_tseitin_0 @ X17 @ X18)
% 2.19/2.42          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 2.19/2.42          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.19/2.42  thf('31', plain,
% 2.19/2.42      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.19/2.42         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['29', '30'])).
% 2.19/2.42  thf('32', plain,
% 2.19/2.42      (![X12 : $i, X13 : $i]:
% 2.19/2.42         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.19/2.42  thf('33', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 2.19/2.42      inference('simplify', [status(thm)], ['32'])).
% 2.19/2.42  thf('34', plain,
% 2.19/2.42      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['31', '33'])).
% 2.19/2.42  thf('35', plain,
% 2.19/2.42      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['28', '34'])).
% 2.19/2.42  thf(t132_partfun1, axiom,
% 2.19/2.42    (![A:$i]:
% 2.19/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.19/2.42       ( ![B:$i]:
% 2.19/2.42         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.19/2.42           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 2.19/2.42             ( ( r1_partfun1 @ A @ B ) <=>
% 2.19/2.42               ( ![C:$i]:
% 2.19/2.42                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.19/2.42                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 2.19/2.42  thf('36', plain,
% 2.19/2.42      (![X20 : $i, X21 : $i]:
% 2.19/2.42         (~ (v1_relat_1 @ X20)
% 2.19/2.42          | ~ (v1_funct_1 @ X20)
% 2.19/2.42          | (r2_hidden @ (sk_C @ X20 @ X21) @ (k1_relat_1 @ X21))
% 2.19/2.42          | (r1_partfun1 @ X21 @ X20)
% 2.19/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.19/2.42          | ~ (v1_funct_1 @ X21)
% 2.19/2.42          | ~ (v1_relat_1 @ X21))),
% 2.19/2.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.19/2.42  thf('37', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | (r1_partfun1 @ X0 @ sk_D)
% 2.19/2.42           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 2.19/2.42           | ~ (v1_funct_1 @ sk_D)
% 2.19/2.42           | ~ (v1_relat_1 @ sk_D)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['35', '36'])).
% 2.19/2.42  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('39', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf(cc1_relset_1, axiom,
% 2.19/2.42    (![A:$i,B:$i,C:$i]:
% 2.19/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.19/2.42       ( v1_relat_1 @ C ) ))).
% 2.19/2.42  thf('40', plain,
% 2.19/2.42      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.19/2.42         ((v1_relat_1 @ X3)
% 2.19/2.42          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.19/2.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.19/2.42  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 2.19/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.42  thf('42', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | (r1_partfun1 @ X0 @ sk_D)
% 2.19/2.42           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['37', '38', '41'])).
% 2.19/2.42  thf('43', plain,
% 2.19/2.42      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ~ (v1_funct_1 @ sk_C_1)
% 2.19/2.42         | ~ (v1_relat_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['17', '42'])).
% 2.19/2.42  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('45', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('46', plain,
% 2.19/2.42      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.19/2.42         ((v1_relat_1 @ X3)
% 2.19/2.42          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.19/2.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.19/2.42  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 2.19/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.19/2.42  thf('48', plain,
% 2.19/2.42      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['43', '44', '47'])).
% 2.19/2.42  thf('49', plain,
% 2.19/2.42      (![X23 : $i]:
% 2.19/2.42         (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42          | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))
% 2.19/2.42          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('50', plain,
% 2.19/2.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('sup-', [status(thm)], ['2', '3'])).
% 2.19/2.42  thf('51', plain,
% 2.19/2.42      (![X23 : $i]:
% 2.19/2.42         (~ (r2_hidden @ X23 @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42          | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))
% 2.19/2.42          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('demod', [status(thm)], ['49', '50'])).
% 2.19/2.42  thf('52', plain,
% 2.19/2.42      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['48', '51'])).
% 2.19/2.42  thf('53', plain,
% 2.19/2.42      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42           = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('simplify', [status(thm)], ['52'])).
% 2.19/2.42  thf('54', plain,
% 2.19/2.42      (![X20 : $i, X21 : $i]:
% 2.19/2.42         (~ (v1_relat_1 @ X20)
% 2.19/2.42          | ~ (v1_funct_1 @ X20)
% 2.19/2.42          | ((k1_funct_1 @ X21 @ (sk_C @ X20 @ X21))
% 2.19/2.42              != (k1_funct_1 @ X20 @ (sk_C @ X20 @ X21)))
% 2.19/2.42          | (r1_partfun1 @ X21 @ X20)
% 2.19/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.19/2.42          | ~ (v1_funct_1 @ X21)
% 2.19/2.42          | ~ (v1_relat_1 @ X21))),
% 2.19/2.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.19/2.42  thf('55', plain,
% 2.19/2.42      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ~ (v1_relat_1 @ sk_C_1)
% 2.19/2.42         | ~ (v1_funct_1 @ sk_C_1)
% 2.19/2.42         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ~ (v1_funct_1 @ sk_D)
% 2.19/2.42         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['53', '54'])).
% 2.19/2.42  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 2.19/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.19/2.42  thf('57', plain, ((v1_funct_1 @ sk_C_1)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('58', plain,
% 2.19/2.42      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['28', '34'])).
% 2.19/2.42  thf('59', plain,
% 2.19/2.42      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['13', '16'])).
% 2.19/2.42  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 2.19/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.42  thf('62', plain,
% 2.19/2.42      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)],
% 2.19/2.42                ['55', '56', '57', '58', '59', '60', '61'])).
% 2.19/2.42  thf('63', plain,
% 2.19/2.42      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('simplify', [status(thm)], ['62'])).
% 2.19/2.42  thf('64', plain,
% 2.19/2.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 2.19/2.42        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('65', plain,
% 2.19/2.42      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 2.19/2.42      inference('split', [status(esa)], ['64'])).
% 2.19/2.42  thf('66', plain,
% 2.19/2.42      (((r1_partfun1 @ sk_C_1 @ sk_D)) | ~ (((sk_A) = (k1_xboole_0)))),
% 2.19/2.42      inference('sup-', [status(thm)], ['63', '65'])).
% 2.19/2.42  thf('67', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('68', plain,
% 2.19/2.42      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.19/2.42         ((m1_subset_1 @ (k1_relset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 2.19/2.42          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 2.19/2.42      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 2.19/2.42  thf('69', plain,
% 2.19/2.42      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 2.19/2.42        (k1_zfmisc_1 @ sk_A))),
% 2.19/2.42      inference('sup-', [status(thm)], ['67', '68'])).
% 2.19/2.42  thf('70', plain,
% 2.19/2.42      (![X0 : $i, X1 : $i]:
% 2.19/2.42         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 2.19/2.42      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.42  thf('71', plain, ((r1_tarski @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 2.19/2.42      inference('sup-', [status(thm)], ['69', '70'])).
% 2.19/2.42  thf('72', plain,
% 2.19/2.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('sup-', [status(thm)], ['2', '3'])).
% 2.19/2.42  thf('73', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.19/2.42      inference('demod', [status(thm)], ['71', '72'])).
% 2.19/2.42  thf('74', plain,
% 2.19/2.42      (![X12 : $i, X13 : $i]:
% 2.19/2.42         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.19/2.42  thf('75', plain,
% 2.19/2.42      (![X12 : $i, X13 : $i]:
% 2.19/2.42         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.19/2.42  thf('76', plain,
% 2.19/2.42      (![X12 : $i, X13 : $i]:
% 2.19/2.42         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.19/2.42  thf('77', plain,
% 2.19/2.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.19/2.42         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 2.19/2.42      inference('sup+', [status(thm)], ['75', '76'])).
% 2.19/2.42  thf('78', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('79', plain,
% 2.19/2.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.19/2.42         (~ (zip_tseitin_0 @ X17 @ X18)
% 2.19/2.42          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 2.19/2.42          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.19/2.42  thf('80', plain,
% 2.19/2.42      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.19/2.42      inference('sup-', [status(thm)], ['78', '79'])).
% 2.19/2.42  thf('81', plain,
% 2.19/2.42      (![X0 : $i, X1 : $i]:
% 2.19/2.42         ((zip_tseitin_0 @ X1 @ X0)
% 2.19/2.42          | ((sk_B) = (X1))
% 2.19/2.42          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 2.19/2.42      inference('sup-', [status(thm)], ['77', '80'])).
% 2.19/2.42  thf('82', plain,
% 2.19/2.42      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('split', [status(esa)], ['6'])).
% 2.19/2.42  thf('83', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i]:
% 2.19/2.42          (((X0) != (k1_xboole_0))
% 2.19/2.42           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 2.19/2.42           | (zip_tseitin_0 @ X0 @ X1)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['81', '82'])).
% 2.19/2.42  thf('84', plain,
% 2.19/2.42      ((![X1 : $i]:
% 2.19/2.42          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 2.19/2.42           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('simplify', [status(thm)], ['83'])).
% 2.19/2.42  thf('85', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('86', plain,
% 2.19/2.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.19/2.42         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 2.19/2.42          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.19/2.42          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.19/2.42  thf('87', plain,
% 2.19/2.42      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 2.19/2.42        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 2.19/2.42      inference('sup-', [status(thm)], ['85', '86'])).
% 2.19/2.42  thf('88', plain,
% 2.19/2.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('89', plain,
% 2.19/2.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.19/2.42         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.19/2.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.19/2.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.19/2.42  thf('90', plain,
% 2.19/2.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.19/2.42      inference('sup-', [status(thm)], ['88', '89'])).
% 2.19/2.42  thf('91', plain,
% 2.19/2.42      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.19/2.42      inference('demod', [status(thm)], ['87', '90'])).
% 2.19/2.42  thf('92', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['84', '91'])).
% 2.19/2.42  thf('93', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.42          ((zip_tseitin_0 @ X0 @ X1)
% 2.19/2.42           | (zip_tseitin_0 @ X0 @ X2)
% 2.19/2.42           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup+', [status(thm)], ['74', '92'])).
% 2.19/2.42  thf('94', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i]:
% 2.19/2.42          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('condensation', [status(thm)], ['93'])).
% 2.19/2.42  thf('95', plain,
% 2.19/2.42      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.19/2.42      inference('sup-', [status(thm)], ['78', '79'])).
% 2.19/2.42  thf('96', plain,
% 2.19/2.42      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['94', '95'])).
% 2.19/2.42  thf('97', plain,
% 2.19/2.42      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.19/2.42      inference('demod', [status(thm)], ['87', '90'])).
% 2.19/2.42  thf('98', plain,
% 2.19/2.42      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('clc', [status(thm)], ['96', '97'])).
% 2.19/2.42  thf('99', plain,
% 2.19/2.42      (![X20 : $i, X21 : $i]:
% 2.19/2.42         (~ (v1_relat_1 @ X20)
% 2.19/2.42          | ~ (v1_funct_1 @ X20)
% 2.19/2.42          | (r2_hidden @ (sk_C @ X20 @ X21) @ (k1_relat_1 @ X21))
% 2.19/2.42          | (r1_partfun1 @ X21 @ X20)
% 2.19/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.19/2.42          | ~ (v1_funct_1 @ X21)
% 2.19/2.42          | ~ (v1_relat_1 @ X21))),
% 2.19/2.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.19/2.42  thf('100', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | (r1_partfun1 @ X0 @ sk_D)
% 2.19/2.42           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 2.19/2.42           | ~ (v1_funct_1 @ sk_D)
% 2.19/2.42           | ~ (v1_relat_1 @ sk_D)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['98', '99'])).
% 2.19/2.42  thf('101', plain, ((v1_funct_1 @ sk_D)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 2.19/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.42  thf('103', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | (r1_partfun1 @ X0 @ sk_D)
% 2.19/2.42           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['100', '101', '102'])).
% 2.19/2.42  thf('104', plain,
% 2.19/2.42      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ~ (v1_funct_1 @ sk_C_1)
% 2.19/2.42         | ~ (v1_relat_1 @ sk_C_1))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['73', '103'])).
% 2.19/2.42  thf('105', plain, ((v1_funct_1 @ sk_C_1)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('106', plain, ((v1_relat_1 @ sk_C_1)),
% 2.19/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.19/2.42  thf('107', plain,
% 2.19/2.42      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['104', '105', '106'])).
% 2.19/2.42  thf('108', plain,
% 2.19/2.42      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('sup-', [status(thm)], ['2', '3'])).
% 2.19/2.42  thf('109', plain,
% 2.19/2.42      (![X23 : $i]:
% 2.19/2.42         (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42          | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))
% 2.19/2.42          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('110', plain,
% 2.19/2.42      ((![X23 : $i]:
% 2.19/2.42          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))))
% 2.19/2.42         <= ((![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('split', [status(esa)], ['109'])).
% 2.19/2.42  thf('111', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 2.19/2.42         <= ((![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['108', '110'])).
% 2.19/2.42  thf('112', plain,
% 2.19/2.42      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.19/2.42             (![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['107', '111'])).
% 2.19/2.42  thf('113', plain,
% 2.19/2.42      (![X20 : $i, X21 : $i]:
% 2.19/2.42         (~ (v1_relat_1 @ X20)
% 2.19/2.42          | ~ (v1_funct_1 @ X20)
% 2.19/2.42          | ((k1_funct_1 @ X21 @ (sk_C @ X20 @ X21))
% 2.19/2.42              != (k1_funct_1 @ X20 @ (sk_C @ X20 @ X21)))
% 2.19/2.42          | (r1_partfun1 @ X21 @ X20)
% 2.19/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.19/2.42          | ~ (v1_funct_1 @ X21)
% 2.19/2.42          | ~ (v1_relat_1 @ X21))),
% 2.19/2.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.19/2.42  thf('114', plain,
% 2.19/2.42      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ~ (v1_relat_1 @ sk_C_1)
% 2.19/2.42         | ~ (v1_funct_1 @ sk_C_1)
% 2.19/2.42         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | ~ (v1_funct_1 @ sk_D)
% 2.19/2.42         | ~ (v1_relat_1 @ sk_D)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.19/2.42             (![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['112', '113'])).
% 2.19/2.42  thf('115', plain, ((v1_relat_1 @ sk_C_1)),
% 2.19/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.19/2.42  thf('116', plain, ((v1_funct_1 @ sk_C_1)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('117', plain,
% 2.19/2.42      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('clc', [status(thm)], ['96', '97'])).
% 2.19/2.42  thf('118', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.19/2.42      inference('demod', [status(thm)], ['71', '72'])).
% 2.19/2.42  thf('119', plain, ((v1_funct_1 @ sk_D)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('120', plain, ((v1_relat_1 @ sk_D)),
% 2.19/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.42  thf('121', plain,
% 2.19/2.42      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.19/2.42           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42         | (r1_partfun1 @ sk_C_1 @ sk_D)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.19/2.42             (![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('demod', [status(thm)],
% 2.19/2.42                ['114', '115', '116', '117', '118', '119', '120'])).
% 2.19/2.42  thf('122', plain,
% 2.19/2.42      (((r1_partfun1 @ sk_C_1 @ sk_D))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.19/2.42             (![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('simplify', [status(thm)], ['121'])).
% 2.19/2.42  thf('123', plain,
% 2.19/2.42      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 2.19/2.42      inference('split', [status(esa)], ['64'])).
% 2.19/2.42  thf('124', plain,
% 2.19/2.42      ((((sk_B) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 2.19/2.42       ~
% 2.19/2.42       (![X23 : $i]:
% 2.19/2.42          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['122', '123'])).
% 2.19/2.42  thf('125', plain,
% 2.19/2.42      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 2.19/2.42       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('split', [status(esa)], ['64'])).
% 2.19/2.42  thf('126', plain,
% 2.19/2.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.19/2.42         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.19/2.42      inference('split', [status(esa)], ['0'])).
% 2.19/2.42  thf('127', plain,
% 2.19/2.42      ((![X23 : $i]:
% 2.19/2.42          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))))
% 2.19/2.42         <= ((![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('split', [status(esa)], ['109'])).
% 2.19/2.42  thf('128', plain,
% 2.19/2.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 2.19/2.42         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 2.19/2.42             (![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['126', '127'])).
% 2.19/2.42  thf('129', plain,
% 2.19/2.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 2.19/2.42         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 2.19/2.42      inference('split', [status(esa)], ['64'])).
% 2.19/2.42  thf('130', plain,
% 2.19/2.42      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 2.19/2.42         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 2.19/2.42             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 2.19/2.42             (![X23 : $i]:
% 2.19/2.42                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42                 | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['128', '129'])).
% 2.19/2.42  thf('131', plain,
% 2.19/2.42      (~
% 2.19/2.42       (![X23 : $i]:
% 2.19/2.42          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23)))) | 
% 2.19/2.42       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 2.19/2.42       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.19/2.42      inference('simplify', [status(thm)], ['130'])).
% 2.19/2.42  thf('132', plain,
% 2.19/2.42      ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 2.19/2.42      inference('split', [status(esa)], ['6'])).
% 2.19/2.42  thf('133', plain,
% 2.19/2.42      (((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 2.19/2.42       (![X23 : $i]:
% 2.19/2.42          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X23) = (k1_funct_1 @ sk_D @ X23))))),
% 2.19/2.42      inference('split', [status(esa)], ['109'])).
% 2.19/2.42  thf('134', plain,
% 2.19/2.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 2.19/2.42       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('split', [status(esa)], ['0'])).
% 2.19/2.42  thf('135', plain,
% 2.19/2.42      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.19/2.42      inference('sat_resolution*', [status(thm)],
% 2.19/2.42                ['66', '124', '125', '131', '132', '133', '134'])).
% 2.19/2.42  thf('136', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['5', '135'])).
% 2.19/2.42  thf('137', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.19/2.42      inference('demod', [status(thm)], ['71', '72'])).
% 2.19/2.42  thf('138', plain,
% 2.19/2.42      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('clc', [status(thm)], ['96', '97'])).
% 2.19/2.42  thf('139', plain,
% 2.19/2.42      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.19/2.42         (~ (v1_relat_1 @ X20)
% 2.19/2.42          | ~ (v1_funct_1 @ X20)
% 2.19/2.42          | ~ (r1_partfun1 @ X21 @ X20)
% 2.19/2.42          | ((k1_funct_1 @ X21 @ X22) = (k1_funct_1 @ X20 @ X22))
% 2.19/2.42          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 2.19/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.19/2.42          | ~ (v1_funct_1 @ X21)
% 2.19/2.42          | ~ (v1_relat_1 @ X21))),
% 2.19/2.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.19/2.42  thf('140', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.19/2.42           | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.19/2.42           | ~ (v1_funct_1 @ sk_D)
% 2.19/2.42           | ~ (v1_relat_1 @ sk_D)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['138', '139'])).
% 2.19/2.42  thf('141', plain, ((v1_funct_1 @ sk_D)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 2.19/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.42  thf('143', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.19/2.42           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 2.19/2.42         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['140', '141', '142'])).
% 2.19/2.42  thf('144', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['5', '135'])).
% 2.19/2.42  thf('145', plain,
% 2.19/2.42      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['13', '16'])).
% 2.19/2.42  thf('146', plain,
% 2.19/2.42      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['28', '34'])).
% 2.19/2.42  thf('147', plain,
% 2.19/2.42      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.19/2.42         (~ (v1_relat_1 @ X20)
% 2.19/2.42          | ~ (v1_funct_1 @ X20)
% 2.19/2.42          | ~ (r1_partfun1 @ X21 @ X20)
% 2.19/2.42          | ((k1_funct_1 @ X21 @ X22) = (k1_funct_1 @ X20 @ X22))
% 2.19/2.42          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 2.19/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.19/2.42          | ~ (v1_funct_1 @ X21)
% 2.19/2.42          | ~ (v1_relat_1 @ X21))),
% 2.19/2.42      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.19/2.42  thf('148', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.19/2.42           | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.19/2.42           | ~ (v1_funct_1 @ sk_D)
% 2.19/2.42           | ~ (v1_relat_1 @ sk_D)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['146', '147'])).
% 2.19/2.42  thf('149', plain, ((v1_funct_1 @ sk_D)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 2.19/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.42  thf('151', plain,
% 2.19/2.42      ((![X0 : $i, X1 : $i]:
% 2.19/2.42          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.19/2.42           | ~ (v1_relat_1 @ X0)
% 2.19/2.42           | ~ (v1_funct_1 @ X0)
% 2.19/2.42           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.42           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.19/2.42           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['148', '149', '150'])).
% 2.19/2.42  thf('152', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.19/2.42           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42           | ~ (v1_funct_1 @ sk_C_1)
% 2.19/2.42           | ~ (v1_relat_1 @ sk_C_1)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['145', '151'])).
% 2.19/2.42  thf('153', plain,
% 2.19/2.42      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= (((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 2.19/2.42      inference('split', [status(esa)], ['109'])).
% 2.19/2.42  thf('154', plain, (((r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.19/2.42      inference('sat_resolution*', [status(thm)],
% 2.19/2.42                ['66', '124', '125', '134', '131', '132', '133'])).
% 2.19/2.42  thf('155', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['153', '154'])).
% 2.19/2.42  thf('156', plain, ((v1_funct_1 @ sk_C_1)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('157', plain, ((v1_relat_1 @ sk_C_1)),
% 2.19/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.19/2.42  thf('158', plain,
% 2.19/2.42      ((![X0 : $i]:
% 2.19/2.42          (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.19/2.42           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('demod', [status(thm)], ['152', '155', '156', '157'])).
% 2.19/2.42  thf('159', plain,
% 2.19/2.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 2.19/2.42         <= ((((sk_A) = (k1_xboole_0))))),
% 2.19/2.42      inference('sup-', [status(thm)], ['144', '158'])).
% 2.19/2.42  thf('160', plain,
% 2.19/2.42      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 2.19/2.42         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 2.19/2.42      inference('split', [status(esa)], ['64'])).
% 2.19/2.42  thf('161', plain,
% 2.19/2.42      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 2.19/2.42      inference('sat_resolution*', [status(thm)],
% 2.19/2.42                ['66', '124', '134', '131', '132', '133', '125'])).
% 2.19/2.42  thf('162', plain,
% 2.19/2.42      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['160', '161'])).
% 2.19/2.42  thf('163', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 2.19/2.42      inference('simplify_reflect-', [status(thm)], ['159', '162'])).
% 2.19/2.42  thf('164', plain,
% 2.19/2.42      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.19/2.42      inference('split', [status(esa)], ['6'])).
% 2.19/2.42  thf('165', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 2.19/2.42      inference('sat_resolution*', [status(thm)], ['163', '164'])).
% 2.19/2.42  thf('166', plain,
% 2.19/2.42      (![X0 : $i, X1 : $i]:
% 2.19/2.42         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.19/2.42          | ~ (v1_relat_1 @ X0)
% 2.19/2.42          | ~ (v1_funct_1 @ X0)
% 2.19/2.42          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.19/2.42          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.19/2.42          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['143', '165'])).
% 2.19/2.42  thf('167', plain,
% 2.19/2.42      (![X0 : $i]:
% 2.19/2.42         (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.19/2.42          | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.19/2.42          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 2.19/2.42          | ~ (v1_funct_1 @ sk_C_1)
% 2.19/2.42          | ~ (v1_relat_1 @ sk_C_1))),
% 2.19/2.42      inference('sup-', [status(thm)], ['137', '166'])).
% 2.19/2.42  thf('168', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['153', '154'])).
% 2.19/2.42  thf('169', plain, ((v1_funct_1 @ sk_C_1)),
% 2.19/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.42  thf('170', plain, ((v1_relat_1 @ sk_C_1)),
% 2.19/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.19/2.42  thf('171', plain,
% 2.19/2.42      (![X0 : $i]:
% 2.19/2.42         (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.19/2.42          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 2.19/2.42      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 2.19/2.42  thf('172', plain,
% 2.19/2.42      (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))),
% 2.19/2.42      inference('sup-', [status(thm)], ['136', '171'])).
% 2.19/2.42  thf('173', plain,
% 2.19/2.42      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 2.19/2.42      inference('simpl_trail', [status(thm)], ['160', '161'])).
% 2.19/2.42  thf('174', plain, ($false),
% 2.19/2.42      inference('simplify_reflect-', [status(thm)], ['172', '173'])).
% 2.19/2.42  
% 2.19/2.42  % SZS output end Refutation
% 2.19/2.42  
% 2.19/2.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
