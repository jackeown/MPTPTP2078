%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IEobxMMrBv

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:13 EST 2020

% Result     : Theorem 2.89s
% Output     : Refutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  214 (3051 expanded)
%              Number of leaves         :   36 ( 868 expanded)
%              Depth                    :   31
%              Number of atoms          : 2069 (56499 expanded)
%              Number of equality atoms :  175 (4249 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

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

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('35',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','35'])).

thf('37',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','36'])).

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

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','45'])).

thf('47',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('50',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X25 )
        = ( k1_funct_1 @ sk_D @ X25 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X25 )
        = ( k1_funct_1 @ sk_D @ X25 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
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

thf('57',plain,
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
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','36'])).

thf('61',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('64',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63'])).

thf('65',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('75',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('93',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','94'])).

thf('96',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['95'])).

thf('97',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('98',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('100',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('109',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('111',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X25 )
        = ( k1_funct_1 @ sk_D @ X25 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ! [X25: $i] :
        ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X25 )
          = ( k1_funct_1 @ sk_D @ X25 ) ) )
   <= ! [X25: $i] :
        ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X25 )
          = ( k1_funct_1 @ sk_D @ X25 ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X25: $i] :
        ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X25 )
          = ( k1_funct_1 @ sk_D @ X25 ) ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
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

thf('116',plain,
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
      & ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('118',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('120',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('121',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('123',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122'])).

thf('124',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('128',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,
    ( ! [X25: $i] :
        ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X25 )
          = ( k1_funct_1 @ sk_D @ X25 ) ) )
   <= ! [X25: $i] :
        ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X25 )
          = ( k1_funct_1 @ sk_D @ X25 ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['66'])).

thf('132',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ! [X25: $i] :
          ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X25 )
            = ( k1_funct_1 @ sk_D @ X25 ) ) )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('135',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ! [X25: $i] :
        ( ~ ( r2_hidden @ X25 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X25 )
          = ( k1_funct_1 @ sk_D @ X25 ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('136',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('137',plain,(
    r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['68','126','127','133','134','135','136'])).

thf('138',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','137'])).

thf('139',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('140',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('141',plain,(
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

thf('142',plain,
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
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('145',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','137'])).

thf('147',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('148',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','36'])).

thf('149',plain,(
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

thf('150',plain,
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
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('153',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','153'])).

thf('155',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['111'])).

thf('156',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['68','126','127','136','133','134','135'])).

thf('157',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','157','158','159'])).

thf('161',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['146','160'])).

thf('162',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['66'])).

thf('163',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['68','126','136','133','134','135','127'])).

thf('164',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['162','163'])).

thf('165',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['161','164'])).

thf('166',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('167',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['145','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['139','168'])).

thf('170',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('171',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['138','173'])).

thf('175',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['162','163'])).

thf('176',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IEobxMMrBv
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.89/3.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.89/3.17  % Solved by: fo/fo7.sh
% 2.89/3.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.89/3.17  % done 1135 iterations in 2.663s
% 2.89/3.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.89/3.17  % SZS output start Refutation
% 2.89/3.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.89/3.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.89/3.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.89/3.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.89/3.17  thf(sk_E_type, type, sk_E: $i).
% 2.89/3.17  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 2.89/3.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.89/3.17  thf(sk_B_type, type, sk_B: $i).
% 2.89/3.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.89/3.17  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.89/3.17  thf(sk_D_type, type, sk_D: $i).
% 2.89/3.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.89/3.17  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.89/3.17  thf(sk_A_type, type, sk_A: $i).
% 2.89/3.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.89/3.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.89/3.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.89/3.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.89/3.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.89/3.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.89/3.17  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.89/3.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.89/3.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.89/3.17  thf(t145_funct_2, conjecture,
% 2.89/3.17    (![A:$i,B:$i,C:$i]:
% 2.89/3.17     ( ( ( v1_funct_1 @ C ) & 
% 2.89/3.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.89/3.17       ( ![D:$i]:
% 2.89/3.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.89/3.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.89/3.17           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.17             ( ( r1_partfun1 @ C @ D ) <=>
% 2.89/3.17               ( ![E:$i]:
% 2.89/3.17                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 2.89/3.17                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 2.89/3.17  thf(zf_stmt_0, negated_conjecture,
% 2.89/3.17    (~( ![A:$i,B:$i,C:$i]:
% 2.89/3.17        ( ( ( v1_funct_1 @ C ) & 
% 2.89/3.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.89/3.17          ( ![D:$i]:
% 2.89/3.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.89/3.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.89/3.17              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.17                ( ( r1_partfun1 @ C @ D ) <=>
% 2.89/3.17                  ( ![E:$i]:
% 2.89/3.17                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 2.89/3.17                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 2.89/3.17    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 2.89/3.17  thf('0', plain,
% 2.89/3.17      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('1', plain,
% 2.89/3.17      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.89/3.17         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.89/3.17      inference('split', [status(esa)], ['0'])).
% 2.89/3.17  thf('2', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf(redefinition_k1_relset_1, axiom,
% 2.89/3.17    (![A:$i,B:$i,C:$i]:
% 2.89/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.89/3.17  thf('3', plain,
% 2.89/3.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.89/3.17         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.89/3.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.89/3.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.89/3.17  thf('4', plain,
% 2.89/3.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.17  thf('5', plain,
% 2.89/3.17      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1)))
% 2.89/3.17         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.89/3.17      inference('demod', [status(thm)], ['1', '4'])).
% 2.89/3.17  thf('6', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('7', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('split', [status(esa)], ['6'])).
% 2.89/3.17  thf('8', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('9', plain,
% 2.89/3.17      (((m1_subset_1 @ sk_C_1 @ 
% 2.89/3.17         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup+', [status(thm)], ['7', '8'])).
% 2.89/3.17  thf(cc2_relset_1, axiom,
% 2.89/3.17    (![A:$i,B:$i,C:$i]:
% 2.89/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.17       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.89/3.17  thf('10', plain,
% 2.89/3.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.89/3.17         ((v4_relat_1 @ X6 @ X7)
% 2.89/3.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.89/3.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.89/3.17  thf('11', plain,
% 2.89/3.17      (((v4_relat_1 @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['9', '10'])).
% 2.89/3.17  thf(d18_relat_1, axiom,
% 2.89/3.17    (![A:$i,B:$i]:
% 2.89/3.17     ( ( v1_relat_1 @ B ) =>
% 2.89/3.17       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.89/3.17  thf('12', plain,
% 2.89/3.17      (![X2 : $i, X3 : $i]:
% 2.89/3.17         (~ (v4_relat_1 @ X2 @ X3)
% 2.89/3.17          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 2.89/3.17          | ~ (v1_relat_1 @ X2))),
% 2.89/3.17      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.89/3.17  thf('13', plain,
% 2.89/3.17      (((~ (v1_relat_1 @ sk_C_1)
% 2.89/3.17         | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['11', '12'])).
% 2.89/3.17  thf('14', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf(cc2_relat_1, axiom,
% 2.89/3.17    (![A:$i]:
% 2.89/3.17     ( ( v1_relat_1 @ A ) =>
% 2.89/3.17       ( ![B:$i]:
% 2.89/3.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.89/3.17  thf('15', plain,
% 2.89/3.17      (![X0 : $i, X1 : $i]:
% 2.89/3.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.89/3.17          | (v1_relat_1 @ X0)
% 2.89/3.17          | ~ (v1_relat_1 @ X1))),
% 2.89/3.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.89/3.17  thf('16', plain,
% 2.89/3.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('sup-', [status(thm)], ['14', '15'])).
% 2.89/3.17  thf(fc6_relat_1, axiom,
% 2.89/3.17    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.89/3.17  thf('17', plain,
% 2.89/3.17      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.89/3.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.89/3.17  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('19', plain,
% 2.89/3.17      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['13', '18'])).
% 2.89/3.17  thf('20', plain,
% 2.89/3.17      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('split', [status(esa)], ['6'])).
% 2.89/3.17  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('22', plain,
% 2.89/3.17      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup+', [status(thm)], ['20', '21'])).
% 2.89/3.17  thf(d1_funct_2, axiom,
% 2.89/3.17    (![A:$i,B:$i,C:$i]:
% 2.89/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.89/3.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.89/3.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.89/3.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.89/3.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.89/3.17  thf(zf_stmt_1, axiom,
% 2.89/3.17    (![C:$i,B:$i,A:$i]:
% 2.89/3.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.89/3.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.89/3.17  thf('23', plain,
% 2.89/3.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.89/3.17         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 2.89/3.17          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.89/3.17          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.89/3.17  thf('24', plain,
% 2.89/3.17      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.89/3.17         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['22', '23'])).
% 2.89/3.17  thf('25', plain,
% 2.89/3.17      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('split', [status(esa)], ['6'])).
% 2.89/3.17  thf('26', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('27', plain,
% 2.89/3.17      (((m1_subset_1 @ sk_D @ 
% 2.89/3.17         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup+', [status(thm)], ['25', '26'])).
% 2.89/3.17  thf('28', plain,
% 2.89/3.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.89/3.17         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.89/3.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.89/3.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.89/3.17  thf('29', plain,
% 2.89/3.17      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['27', '28'])).
% 2.89/3.17  thf('30', plain,
% 2.89/3.17      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.89/3.17         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['24', '29'])).
% 2.89/3.17  thf('31', plain,
% 2.89/3.17      (((m1_subset_1 @ sk_D @ 
% 2.89/3.17         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup+', [status(thm)], ['25', '26'])).
% 2.89/3.17  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.89/3.17  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.89/3.17  thf(zf_stmt_4, axiom,
% 2.89/3.17    (![B:$i,A:$i]:
% 2.89/3.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.89/3.17       ( zip_tseitin_0 @ B @ A ) ))).
% 2.89/3.17  thf(zf_stmt_5, axiom,
% 2.89/3.17    (![A:$i,B:$i,C:$i]:
% 2.89/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.89/3.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.89/3.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.89/3.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.89/3.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.89/3.17  thf('32', plain,
% 2.89/3.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.89/3.17         (~ (zip_tseitin_0 @ X17 @ X18)
% 2.89/3.17          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 2.89/3.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.89/3.17  thf('33', plain,
% 2.89/3.17      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 2.89/3.17         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['31', '32'])).
% 2.89/3.17  thf('34', plain,
% 2.89/3.17      (![X12 : $i, X13 : $i]:
% 2.89/3.17         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.89/3.17  thf('35', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 2.89/3.17      inference('simplify', [status(thm)], ['34'])).
% 2.89/3.17  thf('36', plain,
% 2.89/3.17      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['33', '35'])).
% 2.89/3.17  thf('37', plain,
% 2.89/3.17      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['30', '36'])).
% 2.89/3.17  thf(t132_partfun1, axiom,
% 2.89/3.17    (![A:$i]:
% 2.89/3.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.89/3.17       ( ![B:$i]:
% 2.89/3.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.89/3.17           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 2.89/3.17             ( ( r1_partfun1 @ A @ B ) <=>
% 2.89/3.17               ( ![C:$i]:
% 2.89/3.17                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.89/3.17                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 2.89/3.17  thf('38', plain,
% 2.89/3.17      (![X20 : $i, X21 : $i]:
% 2.89/3.17         (~ (v1_relat_1 @ X20)
% 2.89/3.17          | ~ (v1_funct_1 @ X20)
% 2.89/3.17          | (r2_hidden @ (sk_C @ X20 @ X21) @ (k1_relat_1 @ X21))
% 2.89/3.17          | (r1_partfun1 @ X21 @ X20)
% 2.89/3.17          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.89/3.17          | ~ (v1_funct_1 @ X21)
% 2.89/3.17          | ~ (v1_relat_1 @ X21))),
% 2.89/3.17      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.89/3.17  thf('39', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | (r1_partfun1 @ X0 @ sk_D)
% 2.89/3.17           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 2.89/3.17           | ~ (v1_funct_1 @ sk_D)
% 2.89/3.17           | ~ (v1_relat_1 @ sk_D)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['37', '38'])).
% 2.89/3.17  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('41', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('42', plain,
% 2.89/3.17      (![X0 : $i, X1 : $i]:
% 2.89/3.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.89/3.17          | (v1_relat_1 @ X0)
% 2.89/3.17          | ~ (v1_relat_1 @ X1))),
% 2.89/3.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.89/3.17  thf('43', plain,
% 2.89/3.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.89/3.17      inference('sup-', [status(thm)], ['41', '42'])).
% 2.89/3.17  thf('44', plain,
% 2.89/3.17      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.89/3.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.89/3.17  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 2.89/3.17      inference('demod', [status(thm)], ['43', '44'])).
% 2.89/3.17  thf('46', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | (r1_partfun1 @ X0 @ sk_D)
% 2.89/3.17           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['39', '40', '45'])).
% 2.89/3.17  thf('47', plain,
% 2.89/3.17      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ~ (v1_funct_1 @ sk_C_1)
% 2.89/3.17         | ~ (v1_relat_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['19', '46'])).
% 2.89/3.17  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('50', plain,
% 2.89/3.17      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.89/3.17  thf('51', plain,
% 2.89/3.17      (![X25 : $i]:
% 2.89/3.17         (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17          | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))
% 2.89/3.17          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('52', plain,
% 2.89/3.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.17  thf('53', plain,
% 2.89/3.17      (![X25 : $i]:
% 2.89/3.17         (~ (r2_hidden @ X25 @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17          | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))
% 2.89/3.17          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('demod', [status(thm)], ['51', '52'])).
% 2.89/3.17  thf('54', plain,
% 2.89/3.17      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['50', '53'])).
% 2.89/3.17  thf('55', plain,
% 2.89/3.17      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17           = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('simplify', [status(thm)], ['54'])).
% 2.89/3.17  thf('56', plain,
% 2.89/3.17      (![X20 : $i, X21 : $i]:
% 2.89/3.17         (~ (v1_relat_1 @ X20)
% 2.89/3.17          | ~ (v1_funct_1 @ X20)
% 2.89/3.17          | ((k1_funct_1 @ X21 @ (sk_C @ X20 @ X21))
% 2.89/3.17              != (k1_funct_1 @ X20 @ (sk_C @ X20 @ X21)))
% 2.89/3.17          | (r1_partfun1 @ X21 @ X20)
% 2.89/3.17          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.89/3.17          | ~ (v1_funct_1 @ X21)
% 2.89/3.17          | ~ (v1_relat_1 @ X21))),
% 2.89/3.17      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.89/3.17  thf('57', plain,
% 2.89/3.17      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ~ (v1_relat_1 @ sk_C_1)
% 2.89/3.17         | ~ (v1_funct_1 @ sk_C_1)
% 2.89/3.17         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ~ (v1_funct_1 @ sk_D)
% 2.89/3.17         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['55', '56'])).
% 2.89/3.17  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('60', plain,
% 2.89/3.17      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['30', '36'])).
% 2.89/3.17  thf('61', plain,
% 2.89/3.17      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['13', '18'])).
% 2.89/3.17  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 2.89/3.17      inference('demod', [status(thm)], ['43', '44'])).
% 2.89/3.17  thf('64', plain,
% 2.89/3.17      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)],
% 2.89/3.17                ['57', '58', '59', '60', '61', '62', '63'])).
% 2.89/3.17  thf('65', plain,
% 2.89/3.17      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('simplify', [status(thm)], ['64'])).
% 2.89/3.17  thf('66', plain,
% 2.89/3.17      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 2.89/3.17        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('67', plain,
% 2.89/3.17      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 2.89/3.17      inference('split', [status(esa)], ['66'])).
% 2.89/3.17  thf('68', plain,
% 2.89/3.17      (((r1_partfun1 @ sk_C_1 @ sk_D)) | ~ (((sk_A) = (k1_xboole_0)))),
% 2.89/3.17      inference('sup-', [status(thm)], ['65', '67'])).
% 2.89/3.17  thf('69', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('70', plain,
% 2.89/3.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.89/3.17         ((v4_relat_1 @ X6 @ X7)
% 2.89/3.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.89/3.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.89/3.17  thf('71', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 2.89/3.17      inference('sup-', [status(thm)], ['69', '70'])).
% 2.89/3.17  thf('72', plain,
% 2.89/3.17      (![X2 : $i, X3 : $i]:
% 2.89/3.17         (~ (v4_relat_1 @ X2 @ X3)
% 2.89/3.17          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 2.89/3.17          | ~ (v1_relat_1 @ X2))),
% 2.89/3.17      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.89/3.17  thf('73', plain,
% 2.89/3.17      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 2.89/3.17      inference('sup-', [status(thm)], ['71', '72'])).
% 2.89/3.17  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('75', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.89/3.17      inference('demod', [status(thm)], ['73', '74'])).
% 2.89/3.17  thf('76', plain,
% 2.89/3.17      (![X12 : $i, X13 : $i]:
% 2.89/3.17         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.89/3.17  thf('77', plain,
% 2.89/3.17      (![X12 : $i, X13 : $i]:
% 2.89/3.17         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.89/3.17  thf('78', plain,
% 2.89/3.17      (![X12 : $i, X13 : $i]:
% 2.89/3.17         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.89/3.17  thf('79', plain,
% 2.89/3.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.89/3.17         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 2.89/3.17      inference('sup+', [status(thm)], ['77', '78'])).
% 2.89/3.17  thf('80', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('81', plain,
% 2.89/3.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.89/3.17         (~ (zip_tseitin_0 @ X17 @ X18)
% 2.89/3.17          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 2.89/3.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.89/3.17  thf('82', plain,
% 2.89/3.17      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.89/3.17      inference('sup-', [status(thm)], ['80', '81'])).
% 2.89/3.17  thf('83', plain,
% 2.89/3.17      (![X0 : $i, X1 : $i]:
% 2.89/3.17         ((zip_tseitin_0 @ X1 @ X0)
% 2.89/3.17          | ((sk_B) = (X1))
% 2.89/3.17          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 2.89/3.17      inference('sup-', [status(thm)], ['79', '82'])).
% 2.89/3.17  thf('84', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('85', plain,
% 2.89/3.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.89/3.17         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 2.89/3.17          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 2.89/3.17          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.89/3.17  thf('86', plain,
% 2.89/3.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 2.89/3.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 2.89/3.17      inference('sup-', [status(thm)], ['84', '85'])).
% 2.89/3.17  thf('87', plain,
% 2.89/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('88', plain,
% 2.89/3.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.89/3.17         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.89/3.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.89/3.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.89/3.17  thf('89', plain,
% 2.89/3.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.89/3.17      inference('sup-', [status(thm)], ['87', '88'])).
% 2.89/3.17  thf('90', plain,
% 2.89/3.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.89/3.17      inference('demod', [status(thm)], ['86', '89'])).
% 2.89/3.17  thf('91', plain,
% 2.89/3.17      (![X0 : $i, X1 : $i]:
% 2.89/3.17         (((sk_B) = (X0))
% 2.89/3.17          | (zip_tseitin_0 @ X0 @ X1)
% 2.89/3.17          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.89/3.17      inference('sup-', [status(thm)], ['83', '90'])).
% 2.89/3.17  thf('92', plain,
% 2.89/3.17      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('split', [status(esa)], ['6'])).
% 2.89/3.17  thf('93', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i]:
% 2.89/3.17          (((X0) != (k1_xboole_0))
% 2.89/3.17           | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.89/3.17           | (zip_tseitin_0 @ X0 @ X1)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['91', '92'])).
% 2.89/3.17  thf('94', plain,
% 2.89/3.17      ((![X1 : $i]:
% 2.89/3.17          ((zip_tseitin_0 @ k1_xboole_0 @ X1) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('simplify', [status(thm)], ['93'])).
% 2.89/3.17  thf('95', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.89/3.17          ((zip_tseitin_0 @ X0 @ X1)
% 2.89/3.17           | (zip_tseitin_0 @ X0 @ X2)
% 2.89/3.17           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup+', [status(thm)], ['76', '94'])).
% 2.89/3.17  thf('96', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i]:
% 2.89/3.17          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('condensation', [status(thm)], ['95'])).
% 2.89/3.17  thf('97', plain,
% 2.89/3.17      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.89/3.17      inference('sup-', [status(thm)], ['80', '81'])).
% 2.89/3.17  thf('98', plain,
% 2.89/3.17      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['96', '97'])).
% 2.89/3.17  thf('99', plain,
% 2.89/3.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.89/3.17      inference('demod', [status(thm)], ['86', '89'])).
% 2.89/3.17  thf('100', plain,
% 2.89/3.17      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('clc', [status(thm)], ['98', '99'])).
% 2.89/3.17  thf('101', plain,
% 2.89/3.17      (![X20 : $i, X21 : $i]:
% 2.89/3.17         (~ (v1_relat_1 @ X20)
% 2.89/3.17          | ~ (v1_funct_1 @ X20)
% 2.89/3.17          | (r2_hidden @ (sk_C @ X20 @ X21) @ (k1_relat_1 @ X21))
% 2.89/3.17          | (r1_partfun1 @ X21 @ X20)
% 2.89/3.17          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.89/3.17          | ~ (v1_funct_1 @ X21)
% 2.89/3.17          | ~ (v1_relat_1 @ X21))),
% 2.89/3.17      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.89/3.17  thf('102', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | (r1_partfun1 @ X0 @ sk_D)
% 2.89/3.17           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 2.89/3.17           | ~ (v1_funct_1 @ sk_D)
% 2.89/3.17           | ~ (v1_relat_1 @ sk_D)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['100', '101'])).
% 2.89/3.17  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 2.89/3.17      inference('demod', [status(thm)], ['43', '44'])).
% 2.89/3.17  thf('105', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | (r1_partfun1 @ X0 @ sk_D)
% 2.89/3.17           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['102', '103', '104'])).
% 2.89/3.17  thf('106', plain,
% 2.89/3.17      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ~ (v1_funct_1 @ sk_C_1)
% 2.89/3.17         | ~ (v1_relat_1 @ sk_C_1))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['75', '105'])).
% 2.89/3.17  thf('107', plain, ((v1_funct_1 @ sk_C_1)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('108', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('109', plain,
% 2.89/3.17      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['106', '107', '108'])).
% 2.89/3.17  thf('110', plain,
% 2.89/3.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('sup-', [status(thm)], ['2', '3'])).
% 2.89/3.17  thf('111', plain,
% 2.89/3.17      (![X25 : $i]:
% 2.89/3.17         (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17          | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))
% 2.89/3.17          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('112', plain,
% 2.89/3.17      ((![X25 : $i]:
% 2.89/3.17          (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))))
% 2.89/3.17         <= ((![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('split', [status(esa)], ['111'])).
% 2.89/3.17  thf('113', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 2.89/3.17         <= ((![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['110', '112'])).
% 2.89/3.17  thf('114', plain,
% 2.89/3.17      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.89/3.17             (![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['109', '113'])).
% 2.89/3.17  thf('115', plain,
% 2.89/3.17      (![X20 : $i, X21 : $i]:
% 2.89/3.17         (~ (v1_relat_1 @ X20)
% 2.89/3.17          | ~ (v1_funct_1 @ X20)
% 2.89/3.17          | ((k1_funct_1 @ X21 @ (sk_C @ X20 @ X21))
% 2.89/3.17              != (k1_funct_1 @ X20 @ (sk_C @ X20 @ X21)))
% 2.89/3.17          | (r1_partfun1 @ X21 @ X20)
% 2.89/3.17          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.89/3.17          | ~ (v1_funct_1 @ X21)
% 2.89/3.17          | ~ (v1_relat_1 @ X21))),
% 2.89/3.17      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.89/3.17  thf('116', plain,
% 2.89/3.17      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ~ (v1_relat_1 @ sk_C_1)
% 2.89/3.17         | ~ (v1_funct_1 @ sk_C_1)
% 2.89/3.17         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | ~ (v1_funct_1 @ sk_D)
% 2.89/3.17         | ~ (v1_relat_1 @ sk_D)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.89/3.17             (![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['114', '115'])).
% 2.89/3.17  thf('117', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('118', plain, ((v1_funct_1 @ sk_C_1)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('119', plain,
% 2.89/3.17      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('clc', [status(thm)], ['98', '99'])).
% 2.89/3.17  thf('120', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.89/3.17      inference('demod', [status(thm)], ['73', '74'])).
% 2.89/3.17  thf('121', plain, ((v1_funct_1 @ sk_D)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 2.89/3.17      inference('demod', [status(thm)], ['43', '44'])).
% 2.89/3.17  thf('123', plain,
% 2.89/3.17      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 2.89/3.17           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17         | (r1_partfun1 @ sk_C_1 @ sk_D)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.89/3.17             (![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('demod', [status(thm)],
% 2.89/3.17                ['116', '117', '118', '119', '120', '121', '122'])).
% 2.89/3.17  thf('124', plain,
% 2.89/3.17      (((r1_partfun1 @ sk_C_1 @ sk_D))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 2.89/3.17             (![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('simplify', [status(thm)], ['123'])).
% 2.89/3.17  thf('125', plain,
% 2.89/3.17      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 2.89/3.17      inference('split', [status(esa)], ['66'])).
% 2.89/3.17  thf('126', plain,
% 2.89/3.17      ((((sk_B) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 2.89/3.17       ~
% 2.89/3.17       (![X25 : $i]:
% 2.89/3.17          (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['124', '125'])).
% 2.89/3.17  thf('127', plain,
% 2.89/3.17      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 2.89/3.17       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('split', [status(esa)], ['66'])).
% 2.89/3.17  thf('128', plain,
% 2.89/3.17      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 2.89/3.17         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 2.89/3.17      inference('split', [status(esa)], ['0'])).
% 2.89/3.17  thf('129', plain,
% 2.89/3.17      ((![X25 : $i]:
% 2.89/3.17          (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))))
% 2.89/3.17         <= ((![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('split', [status(esa)], ['111'])).
% 2.89/3.17  thf('130', plain,
% 2.89/3.17      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 2.89/3.17         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 2.89/3.17             (![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['128', '129'])).
% 2.89/3.17  thf('131', plain,
% 2.89/3.17      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 2.89/3.17         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 2.89/3.17      inference('split', [status(esa)], ['66'])).
% 2.89/3.17  thf('132', plain,
% 2.89/3.17      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 2.89/3.17         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 2.89/3.17             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 2.89/3.17             (![X25 : $i]:
% 2.89/3.17                (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17                 | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['130', '131'])).
% 2.89/3.17  thf('133', plain,
% 2.89/3.17      (~
% 2.89/3.17       (![X25 : $i]:
% 2.89/3.17          (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25)))) | 
% 2.89/3.17       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 2.89/3.17       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.89/3.17      inference('simplify', [status(thm)], ['132'])).
% 2.89/3.17  thf('134', plain,
% 2.89/3.17      ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 2.89/3.17      inference('split', [status(esa)], ['6'])).
% 2.89/3.17  thf('135', plain,
% 2.89/3.17      (((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 2.89/3.17       (![X25 : $i]:
% 2.89/3.17          (~ (r2_hidden @ X25 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X25) = (k1_funct_1 @ sk_D @ X25))))),
% 2.89/3.17      inference('split', [status(esa)], ['111'])).
% 2.89/3.17  thf('136', plain,
% 2.89/3.17      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 2.89/3.17       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('split', [status(esa)], ['0'])).
% 2.89/3.17  thf('137', plain,
% 2.89/3.17      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 2.89/3.17      inference('sat_resolution*', [status(thm)],
% 2.89/3.17                ['68', '126', '127', '133', '134', '135', '136'])).
% 2.89/3.17  thf('138', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['5', '137'])).
% 2.89/3.17  thf('139', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 2.89/3.17      inference('demod', [status(thm)], ['73', '74'])).
% 2.89/3.17  thf('140', plain,
% 2.89/3.17      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('clc', [status(thm)], ['98', '99'])).
% 2.89/3.17  thf('141', plain,
% 2.89/3.17      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.89/3.17         (~ (v1_relat_1 @ X20)
% 2.89/3.17          | ~ (v1_funct_1 @ X20)
% 2.89/3.17          | ~ (r1_partfun1 @ X21 @ X20)
% 2.89/3.17          | ((k1_funct_1 @ X21 @ X22) = (k1_funct_1 @ X20 @ X22))
% 2.89/3.17          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 2.89/3.17          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.89/3.17          | ~ (v1_funct_1 @ X21)
% 2.89/3.17          | ~ (v1_relat_1 @ X21))),
% 2.89/3.17      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.89/3.17  thf('142', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.89/3.17           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.89/3.17           | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.89/3.17           | ~ (v1_funct_1 @ sk_D)
% 2.89/3.17           | ~ (v1_relat_1 @ sk_D)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['140', '141'])).
% 2.89/3.17  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 2.89/3.17      inference('demod', [status(thm)], ['43', '44'])).
% 2.89/3.17  thf('145', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.89/3.17           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.89/3.17           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 2.89/3.17         <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['142', '143', '144'])).
% 2.89/3.17  thf('146', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['5', '137'])).
% 2.89/3.17  thf('147', plain,
% 2.89/3.17      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['13', '18'])).
% 2.89/3.17  thf('148', plain,
% 2.89/3.17      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['30', '36'])).
% 2.89/3.17  thf('149', plain,
% 2.89/3.17      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.89/3.17         (~ (v1_relat_1 @ X20)
% 2.89/3.17          | ~ (v1_funct_1 @ X20)
% 2.89/3.17          | ~ (r1_partfun1 @ X21 @ X20)
% 2.89/3.17          | ((k1_funct_1 @ X21 @ X22) = (k1_funct_1 @ X20 @ X22))
% 2.89/3.17          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 2.89/3.17          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 2.89/3.17          | ~ (v1_funct_1 @ X21)
% 2.89/3.17          | ~ (v1_relat_1 @ X21))),
% 2.89/3.17      inference('cnf', [status(esa)], [t132_partfun1])).
% 2.89/3.17  thf('150', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.89/3.17           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.89/3.17           | ~ (r1_partfun1 @ X0 @ sk_D)
% 2.89/3.17           | ~ (v1_funct_1 @ sk_D)
% 2.89/3.17           | ~ (v1_relat_1 @ sk_D)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['148', '149'])).
% 2.89/3.17  thf('151', plain, ((v1_funct_1 @ sk_D)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('152', plain, ((v1_relat_1 @ sk_D)),
% 2.89/3.17      inference('demod', [status(thm)], ['43', '44'])).
% 2.89/3.17  thf('153', plain,
% 2.89/3.17      ((![X0 : $i, X1 : $i]:
% 2.89/3.17          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 2.89/3.17           | ~ (v1_relat_1 @ X0)
% 2.89/3.17           | ~ (v1_funct_1 @ X0)
% 2.89/3.17           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.89/3.17           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.89/3.17           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['150', '151', '152'])).
% 2.89/3.17  thf('154', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.89/3.17           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17           | ~ (v1_funct_1 @ sk_C_1)
% 2.89/3.17           | ~ (v1_relat_1 @ sk_C_1)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['147', '153'])).
% 2.89/3.17  thf('155', plain,
% 2.89/3.17      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= (((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 2.89/3.17      inference('split', [status(esa)], ['111'])).
% 2.89/3.17  thf('156', plain, (((r1_partfun1 @ sk_C_1 @ sk_D))),
% 2.89/3.17      inference('sat_resolution*', [status(thm)],
% 2.89/3.17                ['68', '126', '127', '136', '133', '134', '135'])).
% 2.89/3.17  thf('157', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 2.89/3.17  thf('158', plain, ((v1_funct_1 @ sk_C_1)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('159', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('160', plain,
% 2.89/3.17      ((![X0 : $i]:
% 2.89/3.17          (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.89/3.17           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('demod', [status(thm)], ['154', '157', '158', '159'])).
% 2.89/3.17  thf('161', plain,
% 2.89/3.17      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 2.89/3.17         <= ((((sk_A) = (k1_xboole_0))))),
% 2.89/3.17      inference('sup-', [status(thm)], ['146', '160'])).
% 2.89/3.17  thf('162', plain,
% 2.89/3.17      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 2.89/3.17         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 2.89/3.17      inference('split', [status(esa)], ['66'])).
% 2.89/3.17  thf('163', plain,
% 2.89/3.17      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 2.89/3.17      inference('sat_resolution*', [status(thm)],
% 2.89/3.17                ['68', '126', '136', '133', '134', '135', '127'])).
% 2.89/3.17  thf('164', plain,
% 2.89/3.17      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['162', '163'])).
% 2.89/3.17  thf('165', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 2.89/3.17      inference('simplify_reflect-', [status(thm)], ['161', '164'])).
% 2.89/3.17  thf('166', plain,
% 2.89/3.17      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.89/3.17      inference('split', [status(esa)], ['6'])).
% 2.89/3.17  thf('167', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 2.89/3.17      inference('sat_resolution*', [status(thm)], ['165', '166'])).
% 2.89/3.17  thf('168', plain,
% 2.89/3.17      (![X0 : $i, X1 : $i]:
% 2.89/3.17         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 2.89/3.17          | ~ (v1_relat_1 @ X0)
% 2.89/3.17          | ~ (v1_funct_1 @ X0)
% 2.89/3.17          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.89/3.17          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 2.89/3.17          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['145', '167'])).
% 2.89/3.17  thf('169', plain,
% 2.89/3.17      (![X0 : $i]:
% 2.89/3.17         (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 2.89/3.17          | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.89/3.17          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 2.89/3.17          | ~ (v1_funct_1 @ sk_C_1)
% 2.89/3.17          | ~ (v1_relat_1 @ sk_C_1))),
% 2.89/3.17      inference('sup-', [status(thm)], ['139', '168'])).
% 2.89/3.17  thf('170', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 2.89/3.17  thf('171', plain, ((v1_funct_1 @ sk_C_1)),
% 2.89/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.89/3.17  thf('172', plain, ((v1_relat_1 @ sk_C_1)),
% 2.89/3.17      inference('demod', [status(thm)], ['16', '17'])).
% 2.89/3.17  thf('173', plain,
% 2.89/3.17      (![X0 : $i]:
% 2.89/3.17         (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 2.89/3.17          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 2.89/3.17      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 2.89/3.17  thf('174', plain,
% 2.89/3.17      (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))),
% 2.89/3.17      inference('sup-', [status(thm)], ['138', '173'])).
% 2.89/3.17  thf('175', plain,
% 2.89/3.17      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 2.89/3.17      inference('simpl_trail', [status(thm)], ['162', '163'])).
% 2.89/3.17  thf('176', plain, ($false),
% 2.89/3.17      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 2.89/3.17  
% 2.89/3.17  % SZS output end Refutation
% 2.89/3.17  
% 2.99/3.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
