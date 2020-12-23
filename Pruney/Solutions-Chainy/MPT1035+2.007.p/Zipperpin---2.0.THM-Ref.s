%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FJ0BdRkuRY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:13 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  214 (3051 expanded)
%              Number of leaves         :   36 ( 868 expanded)
%              Depth                    :   31
%              Number of atoms          : 2069 (56499 expanded)
%              Number of equality atoms :  173 (4223 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('35',plain,(
    ! [X15: $i] :
      ( zip_tseitin_0 @ X15 @ k1_xboole_0 ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( sk_C @ X23 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ( r1_partfun1 @ X24 @ X23 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
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
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X26 )
        = ( k1_funct_1 @ sk_D @ X26 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X26 )
        = ( k1_funct_1 @ sk_D @ X26 ) )
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_funct_1 @ X24 @ ( sk_C @ X23 @ X24 ) )
       != ( k1_funct_1 @ X23 @ ( sk_C @ X23 @ X24 ) ) )
      | ( r1_partfun1 @ X24 @ X23 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
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

thf('84',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('92',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','93'])).

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
    inference(demod,[status(thm)],['89','92'])).

thf('100',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( sk_C @ X23 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ( r1_partfun1 @ X24 @ X23 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ X26 )
        = ( k1_funct_1 @ sk_D @ X26 ) )
      | ( r1_partfun1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X26 )
          = ( k1_funct_1 @ sk_D @ X26 ) ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X26 )
          = ( k1_funct_1 @ sk_D @ X26 ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X26 )
          = ( k1_funct_1 @ sk_D @ X26 ) ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( ( ( r1_partfun1 @ sk_C_1 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_funct_1 @ X24 @ ( sk_C @ X23 @ X24 ) )
       != ( k1_funct_1 @ X23 @ ( sk_C @ X23 @ X24 ) ) )
      | ( r1_partfun1 @ X24 @ X23 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
      & ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ) ),
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
      & ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122'])).

thf('124',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ),
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
    ( ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X26 )
          = ( k1_funct_1 @ sk_D @ X26 ) ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X26 )
          = ( k1_funct_1 @ sk_D @ X26 ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ) ),
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
      & ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
          | ( ( k1_funct_1 @ sk_C_1 @ X26 )
            = ( k1_funct_1 @ sk_D @ X26 ) ) )
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
    | ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
        | ( ( k1_funct_1 @ sk_C_1 @ X26 )
          = ( k1_funct_1 @ sk_D @ X26 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( r1_partfun1 @ X24 @ X23 )
      | ( ( k1_funct_1 @ X24 @ X25 )
        = ( k1_funct_1 @ X23 @ X25 ) )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( r1_partfun1 @ X24 @ X23 )
      | ( ( k1_funct_1 @ X24 @ X25 )
        = ( k1_funct_1 @ X23 @ X25 ) )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FJ0BdRkuRY
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.02/3.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.02/3.29  % Solved by: fo/fo7.sh
% 3.02/3.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.02/3.29  % done 2294 iterations in 2.839s
% 3.02/3.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.02/3.29  % SZS output start Refutation
% 3.02/3.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.02/3.29  thf(sk_E_type, type, sk_E: $i).
% 3.02/3.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.02/3.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.02/3.29  thf(sk_D_type, type, sk_D: $i).
% 3.02/3.29  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.02/3.29  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.02/3.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.02/3.29  thf(sk_A_type, type, sk_A: $i).
% 3.02/3.29  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.02/3.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.02/3.29  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 3.02/3.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.02/3.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.02/3.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.02/3.29  thf(sk_B_type, type, sk_B: $i).
% 3.02/3.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.02/3.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.02/3.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.02/3.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.02/3.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.02/3.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.02/3.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.02/3.29  thf(t145_funct_2, conjecture,
% 3.02/3.29    (![A:$i,B:$i,C:$i]:
% 3.02/3.29     ( ( ( v1_funct_1 @ C ) & 
% 3.02/3.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.02/3.29       ( ![D:$i]:
% 3.02/3.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.02/3.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.02/3.29           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.02/3.29             ( ( r1_partfun1 @ C @ D ) <=>
% 3.02/3.29               ( ![E:$i]:
% 3.02/3.29                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 3.02/3.29                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 3.02/3.29  thf(zf_stmt_0, negated_conjecture,
% 3.02/3.29    (~( ![A:$i,B:$i,C:$i]:
% 3.02/3.29        ( ( ( v1_funct_1 @ C ) & 
% 3.02/3.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.02/3.29          ( ![D:$i]:
% 3.02/3.29            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.02/3.29                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.02/3.29              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.02/3.29                ( ( r1_partfun1 @ C @ D ) <=>
% 3.02/3.29                  ( ![E:$i]:
% 3.02/3.29                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 3.02/3.29                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 3.02/3.29    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 3.02/3.29  thf('0', plain,
% 3.02/3.29      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.29        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf('1', plain,
% 3.02/3.29      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 3.02/3.29         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 3.02/3.29      inference('split', [status(esa)], ['0'])).
% 3.02/3.29  thf('2', plain,
% 3.02/3.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf(redefinition_k1_relset_1, axiom,
% 3.02/3.29    (![A:$i,B:$i,C:$i]:
% 3.02/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.02/3.29       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.02/3.29  thf('3', plain,
% 3.02/3.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.02/3.29         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 3.02/3.29          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.02/3.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.02/3.29  thf('4', plain,
% 3.02/3.29      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.02/3.29      inference('sup-', [status(thm)], ['2', '3'])).
% 3.02/3.29  thf('5', plain,
% 3.02/3.29      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1)))
% 3.02/3.29         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 3.02/3.29      inference('demod', [status(thm)], ['1', '4'])).
% 3.02/3.29  thf('6', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf('7', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('split', [status(esa)], ['6'])).
% 3.02/3.29  thf('8', plain,
% 3.02/3.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf('9', plain,
% 3.02/3.29      (((m1_subset_1 @ sk_C_1 @ 
% 3.02/3.29         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup+', [status(thm)], ['7', '8'])).
% 3.02/3.29  thf(cc2_relset_1, axiom,
% 3.02/3.29    (![A:$i,B:$i,C:$i]:
% 3.02/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.02/3.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.02/3.29  thf('10', plain,
% 3.02/3.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.02/3.29         ((v4_relat_1 @ X9 @ X10)
% 3.02/3.29          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.02/3.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.02/3.29  thf('11', plain,
% 3.02/3.29      (((v4_relat_1 @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup-', [status(thm)], ['9', '10'])).
% 3.02/3.29  thf(d18_relat_1, axiom,
% 3.02/3.29    (![A:$i,B:$i]:
% 3.02/3.29     ( ( v1_relat_1 @ B ) =>
% 3.02/3.29       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.02/3.29  thf('12', plain,
% 3.02/3.29      (![X5 : $i, X6 : $i]:
% 3.02/3.29         (~ (v4_relat_1 @ X5 @ X6)
% 3.02/3.29          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.02/3.29          | ~ (v1_relat_1 @ X5))),
% 3.02/3.29      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.02/3.29  thf('13', plain,
% 3.02/3.29      (((~ (v1_relat_1 @ sk_C_1)
% 3.02/3.29         | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0)))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup-', [status(thm)], ['11', '12'])).
% 3.02/3.29  thf('14', plain,
% 3.02/3.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf(cc2_relat_1, axiom,
% 3.02/3.29    (![A:$i]:
% 3.02/3.29     ( ( v1_relat_1 @ A ) =>
% 3.02/3.29       ( ![B:$i]:
% 3.02/3.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.02/3.29  thf('15', plain,
% 3.02/3.29      (![X3 : $i, X4 : $i]:
% 3.02/3.29         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.02/3.29          | (v1_relat_1 @ X3)
% 3.02/3.29          | ~ (v1_relat_1 @ X4))),
% 3.02/3.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.02/3.29  thf('16', plain,
% 3.02/3.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 3.02/3.29      inference('sup-', [status(thm)], ['14', '15'])).
% 3.02/3.29  thf(fc6_relat_1, axiom,
% 3.02/3.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.02/3.29  thf('17', plain,
% 3.02/3.29      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 3.02/3.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.02/3.29  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.29      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.29  thf('19', plain,
% 3.02/3.29      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('demod', [status(thm)], ['13', '18'])).
% 3.02/3.29  thf('20', plain,
% 3.02/3.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('split', [status(esa)], ['6'])).
% 3.02/3.29  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf('22', plain,
% 3.02/3.29      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup+', [status(thm)], ['20', '21'])).
% 3.02/3.29  thf(d1_funct_2, axiom,
% 3.02/3.29    (![A:$i,B:$i,C:$i]:
% 3.02/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.02/3.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.02/3.29           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.02/3.29             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.02/3.29         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.02/3.29           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.02/3.29             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.02/3.29  thf(zf_stmt_1, axiom,
% 3.02/3.29    (![C:$i,B:$i,A:$i]:
% 3.02/3.29     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.02/3.29       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.02/3.29  thf('23', plain,
% 3.02/3.29      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.02/3.29         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 3.02/3.29          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 3.02/3.29          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.02/3.29  thf('24', plain,
% 3.02/3.29      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 3.02/3.29         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup-', [status(thm)], ['22', '23'])).
% 3.02/3.29  thf('25', plain,
% 3.02/3.29      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('split', [status(esa)], ['6'])).
% 3.02/3.29  thf('26', plain,
% 3.02/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.29  thf('27', plain,
% 3.02/3.29      (((m1_subset_1 @ sk_D @ 
% 3.02/3.29         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup+', [status(thm)], ['25', '26'])).
% 3.02/3.29  thf('28', plain,
% 3.02/3.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.02/3.29         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 3.02/3.29          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.02/3.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.02/3.29  thf('29', plain,
% 3.02/3.29      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup-', [status(thm)], ['27', '28'])).
% 3.02/3.29  thf('30', plain,
% 3.02/3.29      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 3.02/3.29         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('demod', [status(thm)], ['24', '29'])).
% 3.02/3.29  thf('31', plain,
% 3.02/3.29      (((m1_subset_1 @ sk_D @ 
% 3.02/3.29         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.02/3.29         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.29      inference('sup+', [status(thm)], ['25', '26'])).
% 3.02/3.29  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.02/3.29  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.02/3.29  thf(zf_stmt_4, axiom,
% 3.02/3.29    (![B:$i,A:$i]:
% 3.02/3.29     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.02/3.29       ( zip_tseitin_0 @ B @ A ) ))).
% 3.02/3.29  thf(zf_stmt_5, axiom,
% 3.02/3.29    (![A:$i,B:$i,C:$i]:
% 3.02/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.02/3.29       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.02/3.29         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.02/3.29           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.02/3.30             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.02/3.30  thf('32', plain,
% 3.02/3.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.02/3.30         (~ (zip_tseitin_0 @ X20 @ X21)
% 3.02/3.30          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 3.02/3.30          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.02/3.30  thf('33', plain,
% 3.02/3.30      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 3.02/3.30         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['31', '32'])).
% 3.02/3.30  thf('34', plain,
% 3.02/3.30      (![X15 : $i, X16 : $i]:
% 3.02/3.30         ((zip_tseitin_0 @ X15 @ X16) | ((X16) != (k1_xboole_0)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.02/3.30  thf('35', plain, (![X15 : $i]: (zip_tseitin_0 @ X15 @ k1_xboole_0)),
% 3.02/3.30      inference('simplify', [status(thm)], ['34'])).
% 3.02/3.30  thf('36', plain,
% 3.02/3.30      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['33', '35'])).
% 3.02/3.30  thf('37', plain,
% 3.02/3.30      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['30', '36'])).
% 3.02/3.30  thf(t132_partfun1, axiom,
% 3.02/3.30    (![A:$i]:
% 3.02/3.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.02/3.30       ( ![B:$i]:
% 3.02/3.30         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.02/3.30           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 3.02/3.30             ( ( r1_partfun1 @ A @ B ) <=>
% 3.02/3.30               ( ![C:$i]:
% 3.02/3.30                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.02/3.30                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 3.02/3.30  thf('38', plain,
% 3.02/3.30      (![X23 : $i, X24 : $i]:
% 3.02/3.30         (~ (v1_relat_1 @ X23)
% 3.02/3.30          | ~ (v1_funct_1 @ X23)
% 3.02/3.30          | (r2_hidden @ (sk_C @ X23 @ X24) @ (k1_relat_1 @ X24))
% 3.02/3.30          | (r1_partfun1 @ X24 @ X23)
% 3.02/3.30          | ~ (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 3.02/3.30          | ~ (v1_funct_1 @ X24)
% 3.02/3.30          | ~ (v1_relat_1 @ X24))),
% 3.02/3.30      inference('cnf', [status(esa)], [t132_partfun1])).
% 3.02/3.30  thf('39', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | (r1_partfun1 @ X0 @ sk_D)
% 3.02/3.30           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 3.02/3.30           | ~ (v1_funct_1 @ sk_D)
% 3.02/3.30           | ~ (v1_relat_1 @ sk_D)))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['37', '38'])).
% 3.02/3.30  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('41', plain,
% 3.02/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('42', plain,
% 3.02/3.30      (![X3 : $i, X4 : $i]:
% 3.02/3.30         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.02/3.30          | (v1_relat_1 @ X3)
% 3.02/3.30          | ~ (v1_relat_1 @ X4))),
% 3.02/3.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.02/3.30  thf('43', plain,
% 3.02/3.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 3.02/3.30      inference('sup-', [status(thm)], ['41', '42'])).
% 3.02/3.30  thf('44', plain,
% 3.02/3.30      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 3.02/3.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.02/3.30  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 3.02/3.30      inference('demod', [status(thm)], ['43', '44'])).
% 3.02/3.30  thf('46', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | (r1_partfun1 @ X0 @ sk_D)
% 3.02/3.30           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['39', '40', '45'])).
% 3.02/3.30  thf('47', plain,
% 3.02/3.30      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ~ (v1_funct_1 @ sk_C_1)
% 3.02/3.30         | ~ (v1_relat_1 @ sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['19', '46'])).
% 3.02/3.30  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('50', plain,
% 3.02/3.30      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['47', '48', '49'])).
% 3.02/3.30  thf('51', plain,
% 3.02/3.30      (![X26 : $i]:
% 3.02/3.30         (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30          | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))
% 3.02/3.30          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('52', plain,
% 3.02/3.30      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.02/3.30      inference('sup-', [status(thm)], ['2', '3'])).
% 3.02/3.30  thf('53', plain,
% 3.02/3.30      (![X26 : $i]:
% 3.02/3.30         (~ (r2_hidden @ X26 @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30          | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))
% 3.02/3.30          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('demod', [status(thm)], ['51', '52'])).
% 3.02/3.30  thf('54', plain,
% 3.02/3.30      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['50', '53'])).
% 3.02/3.30  thf('55', plain,
% 3.02/3.30      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30           = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('simplify', [status(thm)], ['54'])).
% 3.02/3.30  thf('56', plain,
% 3.02/3.30      (![X23 : $i, X24 : $i]:
% 3.02/3.30         (~ (v1_relat_1 @ X23)
% 3.02/3.30          | ~ (v1_funct_1 @ X23)
% 3.02/3.30          | ((k1_funct_1 @ X24 @ (sk_C @ X23 @ X24))
% 3.02/3.30              != (k1_funct_1 @ X23 @ (sk_C @ X23 @ X24)))
% 3.02/3.30          | (r1_partfun1 @ X24 @ X23)
% 3.02/3.30          | ~ (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 3.02/3.30          | ~ (v1_funct_1 @ X24)
% 3.02/3.30          | ~ (v1_relat_1 @ X24))),
% 3.02/3.30      inference('cnf', [status(esa)], [t132_partfun1])).
% 3.02/3.30  thf('57', plain,
% 3.02/3.30      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ~ (v1_relat_1 @ sk_C_1)
% 3.02/3.30         | ~ (v1_funct_1 @ sk_C_1)
% 3.02/3.30         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ~ (v1_funct_1 @ sk_D)
% 3.02/3.30         | ~ (v1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['55', '56'])).
% 3.02/3.30  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('60', plain,
% 3.02/3.30      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['30', '36'])).
% 3.02/3.30  thf('61', plain,
% 3.02/3.30      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['13', '18'])).
% 3.02/3.30  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 3.02/3.30      inference('demod', [status(thm)], ['43', '44'])).
% 3.02/3.30  thf('64', plain,
% 3.02/3.30      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)],
% 3.02/3.30                ['57', '58', '59', '60', '61', '62', '63'])).
% 3.02/3.30  thf('65', plain,
% 3.02/3.30      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('simplify', [status(thm)], ['64'])).
% 3.02/3.30  thf('66', plain,
% 3.02/3.30      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 3.02/3.30        | ~ (r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('67', plain,
% 3.02/3.30      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 3.02/3.30      inference('split', [status(esa)], ['66'])).
% 3.02/3.30  thf('68', plain,
% 3.02/3.30      (((r1_partfun1 @ sk_C_1 @ sk_D)) | ~ (((sk_A) = (k1_xboole_0)))),
% 3.02/3.30      inference('sup-', [status(thm)], ['65', '67'])).
% 3.02/3.30  thf('69', plain,
% 3.02/3.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('70', plain,
% 3.02/3.30      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.02/3.30         ((v4_relat_1 @ X9 @ X10)
% 3.02/3.30          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.02/3.30      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.02/3.30  thf('71', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 3.02/3.30      inference('sup-', [status(thm)], ['69', '70'])).
% 3.02/3.30  thf('72', plain,
% 3.02/3.30      (![X5 : $i, X6 : $i]:
% 3.02/3.30         (~ (v4_relat_1 @ X5 @ X6)
% 3.02/3.30          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.02/3.30          | ~ (v1_relat_1 @ X5))),
% 3.02/3.30      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.02/3.30  thf('73', plain,
% 3.02/3.30      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 3.02/3.30      inference('sup-', [status(thm)], ['71', '72'])).
% 3.02/3.30  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('75', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 3.02/3.30      inference('demod', [status(thm)], ['73', '74'])).
% 3.02/3.30  thf('76', plain,
% 3.02/3.30      (![X15 : $i, X16 : $i]:
% 3.02/3.30         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.02/3.30  thf('77', plain,
% 3.02/3.30      (![X15 : $i, X16 : $i]:
% 3.02/3.30         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.02/3.30  thf('78', plain,
% 3.02/3.30      (![X15 : $i, X16 : $i]:
% 3.02/3.30         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.02/3.30  thf('79', plain,
% 3.02/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.02/3.30         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 3.02/3.30      inference('sup+', [status(thm)], ['77', '78'])).
% 3.02/3.30  thf('80', plain,
% 3.02/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('81', plain,
% 3.02/3.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.02/3.30         (~ (zip_tseitin_0 @ X20 @ X21)
% 3.02/3.30          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 3.02/3.30          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.02/3.30  thf('82', plain,
% 3.02/3.30      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.02/3.30      inference('sup-', [status(thm)], ['80', '81'])).
% 3.02/3.30  thf('83', plain,
% 3.02/3.30      (![X0 : $i, X1 : $i]:
% 3.02/3.30         ((zip_tseitin_0 @ X1 @ X0)
% 3.02/3.30          | ((sk_B) = (X1))
% 3.02/3.30          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.02/3.30      inference('sup-', [status(thm)], ['79', '82'])).
% 3.02/3.30  thf('84', plain,
% 3.02/3.30      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('split', [status(esa)], ['6'])).
% 3.02/3.30  thf('85', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i]:
% 3.02/3.30          (((X0) != (k1_xboole_0))
% 3.02/3.30           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.02/3.30           | (zip_tseitin_0 @ X0 @ X1)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['83', '84'])).
% 3.02/3.30  thf('86', plain,
% 3.02/3.30      ((![X1 : $i]:
% 3.02/3.30          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 3.02/3.30           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('simplify', [status(thm)], ['85'])).
% 3.02/3.30  thf('87', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('88', plain,
% 3.02/3.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.02/3.30         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 3.02/3.30          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 3.02/3.30          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.02/3.30  thf('89', plain,
% 3.02/3.30      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.02/3.30        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.02/3.30      inference('sup-', [status(thm)], ['87', '88'])).
% 3.02/3.30  thf('90', plain,
% 3.02/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('91', plain,
% 3.02/3.30      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.02/3.30         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 3.02/3.30          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.02/3.30      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.02/3.30  thf('92', plain,
% 3.02/3.30      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.02/3.30      inference('sup-', [status(thm)], ['90', '91'])).
% 3.02/3.30  thf('93', plain,
% 3.02/3.30      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.02/3.30      inference('demod', [status(thm)], ['89', '92'])).
% 3.02/3.30  thf('94', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['86', '93'])).
% 3.02/3.30  thf('95', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.30          ((zip_tseitin_0 @ X0 @ X1)
% 3.02/3.30           | (zip_tseitin_0 @ X0 @ X2)
% 3.02/3.30           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup+', [status(thm)], ['76', '94'])).
% 3.02/3.30  thf('96', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i]:
% 3.02/3.30          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('condensation', [status(thm)], ['95'])).
% 3.02/3.30  thf('97', plain,
% 3.02/3.30      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.02/3.30      inference('sup-', [status(thm)], ['80', '81'])).
% 3.02/3.30  thf('98', plain,
% 3.02/3.30      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['96', '97'])).
% 3.02/3.30  thf('99', plain,
% 3.02/3.30      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.02/3.30      inference('demod', [status(thm)], ['89', '92'])).
% 3.02/3.30  thf('100', plain,
% 3.02/3.30      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('clc', [status(thm)], ['98', '99'])).
% 3.02/3.30  thf('101', plain,
% 3.02/3.30      (![X23 : $i, X24 : $i]:
% 3.02/3.30         (~ (v1_relat_1 @ X23)
% 3.02/3.30          | ~ (v1_funct_1 @ X23)
% 3.02/3.30          | (r2_hidden @ (sk_C @ X23 @ X24) @ (k1_relat_1 @ X24))
% 3.02/3.30          | (r1_partfun1 @ X24 @ X23)
% 3.02/3.30          | ~ (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 3.02/3.30          | ~ (v1_funct_1 @ X24)
% 3.02/3.30          | ~ (v1_relat_1 @ X24))),
% 3.02/3.30      inference('cnf', [status(esa)], [t132_partfun1])).
% 3.02/3.30  thf('102', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | (r1_partfun1 @ X0 @ sk_D)
% 3.02/3.30           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 3.02/3.30           | ~ (v1_funct_1 @ sk_D)
% 3.02/3.30           | ~ (v1_relat_1 @ sk_D)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['100', '101'])).
% 3.02/3.30  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 3.02/3.30      inference('demod', [status(thm)], ['43', '44'])).
% 3.02/3.30  thf('105', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | (r1_partfun1 @ X0 @ sk_D)
% 3.02/3.30           | (r2_hidden @ (sk_C @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['102', '103', '104'])).
% 3.02/3.30  thf('106', plain,
% 3.02/3.30      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ~ (v1_funct_1 @ sk_C_1)
% 3.02/3.30         | ~ (v1_relat_1 @ sk_C_1))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['75', '105'])).
% 3.02/3.30  thf('107', plain, ((v1_funct_1 @ sk_C_1)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('108', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('109', plain,
% 3.02/3.30      ((((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['106', '107', '108'])).
% 3.02/3.30  thf('110', plain,
% 3.02/3.30      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.02/3.30      inference('sup-', [status(thm)], ['2', '3'])).
% 3.02/3.30  thf('111', plain,
% 3.02/3.30      (![X26 : $i]:
% 3.02/3.30         (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30          | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))
% 3.02/3.30          | (r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('112', plain,
% 3.02/3.30      ((![X26 : $i]:
% 3.02/3.30          (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))))
% 3.02/3.30         <= ((![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('split', [status(esa)], ['111'])).
% 3.02/3.30  thf('113', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 3.02/3.30         <= ((![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['110', '112'])).
% 3.02/3.30  thf('114', plain,
% 3.02/3.30      ((((r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30             = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 3.02/3.30             (![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['109', '113'])).
% 3.02/3.30  thf('115', plain,
% 3.02/3.30      (![X23 : $i, X24 : $i]:
% 3.02/3.30         (~ (v1_relat_1 @ X23)
% 3.02/3.30          | ~ (v1_funct_1 @ X23)
% 3.02/3.30          | ((k1_funct_1 @ X24 @ (sk_C @ X23 @ X24))
% 3.02/3.30              != (k1_funct_1 @ X23 @ (sk_C @ X23 @ X24)))
% 3.02/3.30          | (r1_partfun1 @ X24 @ X23)
% 3.02/3.30          | ~ (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 3.02/3.30          | ~ (v1_funct_1 @ X24)
% 3.02/3.30          | ~ (v1_relat_1 @ X24))),
% 3.02/3.30      inference('cnf', [status(esa)], [t132_partfun1])).
% 3.02/3.30  thf('116', plain,
% 3.02/3.30      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ~ (v1_relat_1 @ sk_C_1)
% 3.02/3.30         | ~ (v1_funct_1 @ sk_C_1)
% 3.02/3.30         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_D))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | ~ (v1_funct_1 @ sk_D)
% 3.02/3.30         | ~ (v1_relat_1 @ sk_D)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 3.02/3.30             (![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['114', '115'])).
% 3.02/3.30  thf('117', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('118', plain, ((v1_funct_1 @ sk_C_1)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('119', plain,
% 3.02/3.30      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('clc', [status(thm)], ['98', '99'])).
% 3.02/3.30  thf('120', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 3.02/3.30      inference('demod', [status(thm)], ['73', '74'])).
% 3.02/3.30  thf('121', plain, ((v1_funct_1 @ sk_D)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 3.02/3.30      inference('demod', [status(thm)], ['43', '44'])).
% 3.02/3.30  thf('123', plain,
% 3.02/3.30      (((((k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))
% 3.02/3.30           != (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30         | (r1_partfun1 @ sk_C_1 @ sk_D)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 3.02/3.30             (![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('demod', [status(thm)],
% 3.02/3.30                ['116', '117', '118', '119', '120', '121', '122'])).
% 3.02/3.30  thf('124', plain,
% 3.02/3.30      (((r1_partfun1 @ sk_C_1 @ sk_D))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 3.02/3.30             (![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('simplify', [status(thm)], ['123'])).
% 3.02/3.30  thf('125', plain,
% 3.02/3.30      ((~ (r1_partfun1 @ sk_C_1 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 3.02/3.30      inference('split', [status(esa)], ['66'])).
% 3.02/3.30  thf('126', plain,
% 3.02/3.30      ((((sk_B) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 3.02/3.30       ~
% 3.02/3.30       (![X26 : $i]:
% 3.02/3.30          (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['124', '125'])).
% 3.02/3.30  thf('127', plain,
% 3.02/3.30      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 3.02/3.30       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('split', [status(esa)], ['66'])).
% 3.02/3.30  thf('128', plain,
% 3.02/3.30      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 3.02/3.30         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 3.02/3.30      inference('split', [status(esa)], ['0'])).
% 3.02/3.30  thf('129', plain,
% 3.02/3.30      ((![X26 : $i]:
% 3.02/3.30          (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))))
% 3.02/3.30         <= ((![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('split', [status(esa)], ['111'])).
% 3.02/3.30  thf('130', plain,
% 3.02/3.30      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 3.02/3.30         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 3.02/3.30             (![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['128', '129'])).
% 3.02/3.30  thf('131', plain,
% 3.02/3.30      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 3.02/3.30         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 3.02/3.30      inference('split', [status(esa)], ['66'])).
% 3.02/3.30  thf('132', plain,
% 3.02/3.30      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 3.02/3.30         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 3.02/3.30             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 3.02/3.30             (![X26 : $i]:
% 3.02/3.30                (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30                 | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['130', '131'])).
% 3.02/3.30  thf('133', plain,
% 3.02/3.30      (~
% 3.02/3.30       (![X26 : $i]:
% 3.02/3.30          (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26)))) | 
% 3.02/3.30       (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 3.02/3.30       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 3.02/3.30      inference('simplify', [status(thm)], ['132'])).
% 3.02/3.30  thf('134', plain,
% 3.02/3.30      ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 3.02/3.30      inference('split', [status(esa)], ['6'])).
% 3.02/3.30  thf('135', plain,
% 3.02/3.30      (((r1_partfun1 @ sk_C_1 @ sk_D)) | 
% 3.02/3.30       (![X26 : $i]:
% 3.02/3.30          (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X26) = (k1_funct_1 @ sk_D @ X26))))),
% 3.02/3.30      inference('split', [status(esa)], ['111'])).
% 3.02/3.30  thf('136', plain,
% 3.02/3.30      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 3.02/3.30       ~ ((r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('split', [status(esa)], ['0'])).
% 3.02/3.30  thf('137', plain,
% 3.02/3.30      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 3.02/3.30      inference('sat_resolution*', [status(thm)],
% 3.02/3.30                ['68', '126', '127', '133', '134', '135', '136'])).
% 3.02/3.30  thf('138', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['5', '137'])).
% 3.02/3.30  thf('139', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 3.02/3.30      inference('demod', [status(thm)], ['73', '74'])).
% 3.02/3.30  thf('140', plain,
% 3.02/3.30      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('clc', [status(thm)], ['98', '99'])).
% 3.02/3.30  thf('141', plain,
% 3.02/3.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.02/3.30         (~ (v1_relat_1 @ X23)
% 3.02/3.30          | ~ (v1_funct_1 @ X23)
% 3.02/3.30          | ~ (r1_partfun1 @ X24 @ X23)
% 3.02/3.30          | ((k1_funct_1 @ X24 @ X25) = (k1_funct_1 @ X23 @ X25))
% 3.02/3.30          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 3.02/3.30          | ~ (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 3.02/3.30          | ~ (v1_funct_1 @ X24)
% 3.02/3.30          | ~ (v1_relat_1 @ X24))),
% 3.02/3.30      inference('cnf', [status(esa)], [t132_partfun1])).
% 3.02/3.30  thf('142', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.30           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 3.02/3.30           | ~ (r1_partfun1 @ X0 @ sk_D)
% 3.02/3.30           | ~ (v1_funct_1 @ sk_D)
% 3.02/3.30           | ~ (v1_relat_1 @ sk_D)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['140', '141'])).
% 3.02/3.30  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 3.02/3.30      inference('demod', [status(thm)], ['43', '44'])).
% 3.02/3.30  thf('145', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.30           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 3.02/3.30           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 3.02/3.30         <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['142', '143', '144'])).
% 3.02/3.30  thf('146', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_1))),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['5', '137'])).
% 3.02/3.30  thf('147', plain,
% 3.02/3.30      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['13', '18'])).
% 3.02/3.30  thf('148', plain,
% 3.02/3.30      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['30', '36'])).
% 3.02/3.30  thf('149', plain,
% 3.02/3.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.02/3.30         (~ (v1_relat_1 @ X23)
% 3.02/3.30          | ~ (v1_funct_1 @ X23)
% 3.02/3.30          | ~ (r1_partfun1 @ X24 @ X23)
% 3.02/3.30          | ((k1_funct_1 @ X24 @ X25) = (k1_funct_1 @ X23 @ X25))
% 3.02/3.30          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 3.02/3.30          | ~ (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 3.02/3.30          | ~ (v1_funct_1 @ X24)
% 3.02/3.30          | ~ (v1_relat_1 @ X24))),
% 3.02/3.30      inference('cnf', [status(esa)], [t132_partfun1])).
% 3.02/3.30  thf('150', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.30           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 3.02/3.30           | ~ (r1_partfun1 @ X0 @ sk_D)
% 3.02/3.30           | ~ (v1_funct_1 @ sk_D)
% 3.02/3.30           | ~ (v1_relat_1 @ sk_D)))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['148', '149'])).
% 3.02/3.30  thf('151', plain, ((v1_funct_1 @ sk_D)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('152', plain, ((v1_relat_1 @ sk_D)),
% 3.02/3.30      inference('demod', [status(thm)], ['43', '44'])).
% 3.02/3.30  thf('153', plain,
% 3.02/3.30      ((![X0 : $i, X1 : $i]:
% 3.02/3.30          (~ (r1_tarski @ (k1_relat_1 @ X0) @ k1_xboole_0)
% 3.02/3.30           | ~ (v1_relat_1 @ X0)
% 3.02/3.30           | ~ (v1_funct_1 @ X0)
% 3.02/3.30           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.30           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 3.02/3.30           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['150', '151', '152'])).
% 3.02/3.30  thf('154', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30           | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 3.02/3.30           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30           | ~ (v1_funct_1 @ sk_C_1)
% 3.02/3.30           | ~ (v1_relat_1 @ sk_C_1)))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['147', '153'])).
% 3.02/3.30  thf('155', plain,
% 3.02/3.30      (((r1_partfun1 @ sk_C_1 @ sk_D)) <= (((r1_partfun1 @ sk_C_1 @ sk_D)))),
% 3.02/3.30      inference('split', [status(esa)], ['111'])).
% 3.02/3.30  thf('156', plain, (((r1_partfun1 @ sk_C_1 @ sk_D))),
% 3.02/3.30      inference('sat_resolution*', [status(thm)],
% 3.02/3.30                ['68', '126', '127', '136', '133', '134', '135'])).
% 3.02/3.30  thf('157', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 3.02/3.30  thf('158', plain, ((v1_funct_1 @ sk_C_1)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('159', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('160', plain,
% 3.02/3.30      ((![X0 : $i]:
% 3.02/3.30          (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 3.02/3.30           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('demod', [status(thm)], ['154', '157', '158', '159'])).
% 3.02/3.30  thf('161', plain,
% 3.02/3.30      ((((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 3.02/3.30         <= ((((sk_A) = (k1_xboole_0))))),
% 3.02/3.30      inference('sup-', [status(thm)], ['146', '160'])).
% 3.02/3.30  thf('162', plain,
% 3.02/3.30      ((((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 3.02/3.30         <= (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 3.02/3.30      inference('split', [status(esa)], ['66'])).
% 3.02/3.30  thf('163', plain,
% 3.02/3.30      (~ (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 3.02/3.30      inference('sat_resolution*', [status(thm)],
% 3.02/3.30                ['68', '126', '136', '133', '134', '135', '127'])).
% 3.02/3.30  thf('164', plain,
% 3.02/3.30      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['162', '163'])).
% 3.02/3.30  thf('165', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.02/3.30      inference('simplify_reflect-', [status(thm)], ['161', '164'])).
% 3.02/3.30  thf('166', plain,
% 3.02/3.30      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.02/3.30      inference('split', [status(esa)], ['6'])).
% 3.02/3.30  thf('167', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 3.02/3.30      inference('sat_resolution*', [status(thm)], ['165', '166'])).
% 3.02/3.30  thf('168', plain,
% 3.02/3.30      (![X0 : $i, X1 : $i]:
% 3.02/3.30         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 3.02/3.30          | ~ (v1_relat_1 @ X0)
% 3.02/3.30          | ~ (v1_funct_1 @ X0)
% 3.02/3.30          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.30          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 3.02/3.30          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['145', '167'])).
% 3.02/3.30  thf('169', plain,
% 3.02/3.30      (![X0 : $i]:
% 3.02/3.30         (~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.02/3.30          | ((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 3.02/3.30          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 3.02/3.30          | ~ (v1_funct_1 @ sk_C_1)
% 3.02/3.30          | ~ (v1_relat_1 @ sk_C_1))),
% 3.02/3.30      inference('sup-', [status(thm)], ['139', '168'])).
% 3.02/3.30  thf('170', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 3.02/3.30  thf('171', plain, ((v1_funct_1 @ sk_C_1)),
% 3.02/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.30  thf('172', plain, ((v1_relat_1 @ sk_C_1)),
% 3.02/3.30      inference('demod', [status(thm)], ['16', '17'])).
% 3.02/3.30  thf('173', plain,
% 3.02/3.30      (![X0 : $i]:
% 3.02/3.30         (((k1_funct_1 @ sk_C_1 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 3.02/3.30          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 3.02/3.30      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 3.02/3.30  thf('174', plain,
% 3.02/3.30      (((k1_funct_1 @ sk_C_1 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))),
% 3.02/3.30      inference('sup-', [status(thm)], ['138', '173'])).
% 3.02/3.30  thf('175', plain,
% 3.02/3.30      (((k1_funct_1 @ sk_C_1 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 3.02/3.30      inference('simpl_trail', [status(thm)], ['162', '163'])).
% 3.02/3.30  thf('176', plain, ($false),
% 3.02/3.30      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 3.02/3.30  
% 3.02/3.30  % SZS output end Refutation
% 3.02/3.30  
% 3.14/3.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
