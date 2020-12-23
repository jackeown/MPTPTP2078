%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxGcl6YpF6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:54 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  152 (2617 expanded)
%              Number of leaves         :   48 ( 747 expanded)
%              Depth                    :   18
%              Number of atoms          : 1006 (29909 expanded)
%              Number of equality atoms :   39 (1166 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ( zip_tseitin_0 @ ( sk_E_2 @ X40 @ X37 @ X38 ) @ X40 @ X37 @ X38 )
      | ( X39
       != ( k1_funct_2 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X37: $i,X38: $i,X40: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_2 @ X40 @ X37 @ X38 ) @ X40 @ X37 @ X38 )
      | ~ ( r2_hidden @ X40 @ ( k1_funct_2 @ X38 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X32 = X30 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_1
    = ( sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_funct_1 @ X30 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X19 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X30 )
        = X33 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( zip_tseitin_0 @ X30 @ X32 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( sk_F @ X20 @ X21 @ X22 ) @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_F @ ( k2_relat_1 @ sk_C_1 ) @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_F @ ( k2_relat_1 @ sk_C_1 ) @ sk_A @ ( sk_B_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,(
    ! [X43: $i] :
      ( ( v1_funct_2 @ X43 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('57',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_partfun1 @ X24 @ X25 )
      | ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('66',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','66'])).

thf('68',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['33','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('71',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('72',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_B_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['69','75'])).

thf('77',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['68','79'])).

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

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('81',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 @ X46 @ X47 )
      | ( r2_hidden @ X44 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ X52 )
       != X51 )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X52 @ X53 @ X51 ) @ X52 @ X53 @ X51 )
      | ( zip_tseitin_2 @ X52 @ X53 @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('86',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ~ ( v1_funct_1 @ X52 )
      | ( zip_tseitin_2 @ X52 @ X53 @ ( k1_relat_1 @ X52 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X52 @ X53 @ ( k1_relat_1 @ X52 ) ) @ X52 @ X53 @ ( k1_relat_1 @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('91',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','66'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('99',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( zip_tseitin_2 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('101',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['80','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxGcl6YpF6
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 595 iterations in 0.539s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.76/0.99  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.76/0.99  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.76/0.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.99  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.76/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.76/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.76/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.76/0.99  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.76/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.99  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.76/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.99  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i).
% 0.76/0.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.99  thf(t121_funct_2, conjecture,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.76/0.99       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.99        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.76/0.99          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      ((~ (v1_funct_1 @ sk_C_1)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.76/0.99        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))
% 0.76/0.99         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('2', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(d2_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.76/0.99       ( ![D:$i]:
% 0.76/0.99         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.99           ( ?[E:$i]:
% 0.76/0.99             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.76/0.99               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.76/0.99               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_2, axiom,
% 0.76/0.99    (![E:$i,D:$i,B:$i,A:$i]:
% 0.76/0.99     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.76/0.99       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.76/0.99         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.76/0.99         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.76/0.99  thf(zf_stmt_3, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.76/0.99       ( ![D:$i]:
% 0.76/0.99         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.99           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.76/0.99         (~ (r2_hidden @ X40 @ X39)
% 0.76/0.99          | (zip_tseitin_0 @ (sk_E_2 @ X40 @ X37 @ X38) @ X40 @ X37 @ X38)
% 0.76/0.99          | ((X39) != (k1_funct_2 @ X38 @ X37)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.99  thf('4', plain,
% 0.76/0.99      (![X37 : $i, X38 : $i, X40 : $i]:
% 0.76/0.99         ((zip_tseitin_0 @ (sk_E_2 @ X40 @ X37 @ X38) @ X40 @ X37 @ X38)
% 0.76/0.99          | ~ (r2_hidden @ X40 @ (k1_funct_2 @ X38 @ X37)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['3'])).
% 0.76/0.99  thf('5', plain,
% 0.76/0.99      ((zip_tseitin_0 @ (sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.76/0.99        sk_A)),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '4'])).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      ((zip_tseitin_0 @ (sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.76/0.99        sk_A)),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '4'])).
% 0.76/0.99  thf('7', plain,
% 0.76/0.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         (((X32) = (X30)) | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.99  thf('8', plain, (((sk_C_1) = (sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.99  thf('9', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.76/0.99      inference('demod', [status(thm)], ['5', '8'])).
% 0.76/0.99  thf('10', plain,
% 0.76/0.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         ((v1_funct_1 @ X30) | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.99  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('12', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('13', plain, (((v1_funct_1 @ sk_C_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.99  thf('14', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.76/0.99      inference('demod', [status(thm)], ['5', '8'])).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         ((r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.76/0.99          | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.99  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.76/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.99  thf(d10_xboole_0, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.99  thf('17', plain,
% 0.76/0.99      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.76/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.99  thf('18', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.76/0.99      inference('simplify', [status(thm)], ['17'])).
% 0.76/0.99  thf(t11_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( v1_relat_1 @ C ) =>
% 0.76/0.99       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.76/0.99           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.99  thf('19', plain,
% 0.76/0.99      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.99         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.76/0.99          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ X19)
% 0.76/0.99          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.76/0.99          | ~ (v1_relat_1 @ X17))),
% 0.76/0.99      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (~ (v1_relat_1 @ X0)
% 0.76/0.99          | (m1_subset_1 @ X0 @ 
% 0.76/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.76/0.99          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.99  thf('21', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_2)))
% 0.76/0.99        | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['16', '20'])).
% 0.76/0.99  thf('22', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.76/0.99      inference('demod', [status(thm)], ['5', '8'])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         (((k1_relat_1 @ X30) = (X33))
% 0.76/0.99          | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.99  thf('24', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf('25', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.76/0.99      inference('demod', [status(thm)], ['5', '8'])).
% 0.76/0.99  thf('26', plain,
% 0.76/0.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         ((v1_relat_1 @ X30) | ~ (zip_tseitin_0 @ X30 @ X32 @ X31 @ X33))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.99  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.99  thf('28', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.76/0.99      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.76/0.99         <= (~
% 0.76/0.99             ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('30', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.99  thf('31', plain,
% 0.76/0.99      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)) | 
% 0.76/0.99       ~
% 0.76/0.99       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))) | 
% 0.76/0.99       ~ ((v1_funct_1 @ sk_C_1))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('32', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))),
% 0.76/0.99      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 0.76/0.99  thf('33', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.76/0.99  thf(t7_xboole_0, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.99          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.99  thf('35', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf(t3_funct_2, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.99       ( ( v1_funct_1 @ A ) & 
% 0.76/0.99         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.76/0.99         ( m1_subset_1 @
% 0.76/0.99           A @ 
% 0.76/0.99           ( k1_zfmisc_1 @
% 0.76/0.99             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.99  thf('36', plain,
% 0.76/0.99      (![X43 : $i]:
% 0.76/0.99         ((m1_subset_1 @ X43 @ 
% 0.76/0.99           (k1_zfmisc_1 @ 
% 0.76/0.99            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 0.76/0.99          | ~ (v1_funct_1 @ X43)
% 0.76/0.99          | ~ (v1_relat_1 @ X43))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.76/0.99  thf('37', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.76/0.99        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C_1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['35', '36'])).
% 0.76/0.99  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('39', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.76/0.99        | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.99      inference('demod', [status(thm)], ['37', '38'])).
% 0.76/0.99  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.99  thf('41', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.76/0.99      inference('demod', [status(thm)], ['39', '40'])).
% 0.76/0.99  thf(t6_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.76/0.99       ( ~( ( r2_hidden @ A @ D ) & 
% 0.76/0.99            ( ![E:$i,F:$i]:
% 0.76/0.99              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.76/0.99                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.76/0.99         ((r2_hidden @ (sk_F @ X20 @ X21 @ X22) @ X20)
% 0.76/0.99          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.76/0.99          | ~ (r2_hidden @ X22 @ X23))),
% 0.76/0.99      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.76/0.99  thf('43', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.76/0.99          | (r2_hidden @ (sk_F @ (k2_relat_1 @ sk_C_1) @ sk_A @ X0) @ 
% 0.76/0.99             (k2_relat_1 @ sk_C_1)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      ((((sk_C_1) = (k1_xboole_0))
% 0.76/0.99        | (r2_hidden @ 
% 0.76/0.99           (sk_F @ (k2_relat_1 @ sk_C_1) @ sk_A @ (sk_B_1 @ sk_C_1)) @ 
% 0.76/0.99           (k2_relat_1 @ sk_C_1)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['34', '43'])).
% 0.76/0.99  thf(d1_xboole_0, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.99  thf('46', plain,
% 0.76/0.99      ((((sk_C_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['44', '45'])).
% 0.76/0.99  thf('47', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.76/0.99      inference('demod', [status(thm)], ['39', '40'])).
% 0.76/0.99  thf(cc5_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.99       ( ![C:$i]:
% 0.76/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.76/0.99             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.76/0.99          | (v1_partfun1 @ X27 @ X28)
% 0.76/0.99          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.76/0.99          | ~ (v1_funct_1 @ X27)
% 0.76/0.99          | (v1_xboole_0 @ X29))),
% 0.76/0.99      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.76/0.99        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.99  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('51', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (![X43 : $i]:
% 0.76/0.99         ((v1_funct_2 @ X43 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))
% 0.76/0.99          | ~ (v1_funct_1 @ X43)
% 0.76/0.99          | ~ (v1_relat_1 @ X43))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.76/0.99        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C_1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['51', '52'])).
% 0.76/0.99  thf('54', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('55', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.76/0.99        | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.99      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.99  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.99  thf('57', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.76/0.99      inference('demod', [status(thm)], ['55', '56'])).
% 0.76/0.99  thf('58', plain,
% 0.76/0.99      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['49', '50', '57'])).
% 0.76/0.99  thf('59', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.76/0.99      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.76/0.99  thf(cc1_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.76/0.99         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.99         (~ (v1_funct_1 @ X24)
% 0.76/0.99          | ~ (v1_partfun1 @ X24 @ X25)
% 0.76/0.99          | (v1_funct_2 @ X24 @ X25 @ X26)
% 0.76/0.99          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.76/0.99      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.76/0.99  thf('61', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.76/0.99        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.99  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('63', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['61', '62'])).
% 0.76/0.99  thf('64', plain,
% 0.76/0.99      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.76/0.99        | (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))),
% 0.76/0.99      inference('sup-', [status(thm)], ['58', '63'])).
% 0.76/0.99  thf('65', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.76/0.99  thf('66', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.76/0.99      inference('clc', [status(thm)], ['64', '65'])).
% 0.76/0.99  thf('67', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['46', '66'])).
% 0.76/0.99  thf('68', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 0.76/0.99      inference('demod', [status(thm)], ['33', '67'])).
% 0.76/0.99  thf('69', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf('70', plain,
% 0.76/0.99      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.99  thf(d4_relat_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.76/0.99       ( ![C:$i]:
% 0.76/0.99         ( ( r2_hidden @ C @ B ) <=>
% 0.76/0.99           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.76/0.99  thf('71', plain,
% 0.76/0.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.76/0.99         (~ (r2_hidden @ X14 @ X13)
% 0.76/0.99          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.76/0.99          | ((X13) != (k1_relat_1 @ X12)))),
% 0.76/0.99      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.76/0.99  thf('72', plain,
% 0.76/0.99      (![X12 : $i, X14 : $i]:
% 0.76/0.99         ((r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.76/0.99          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['71'])).
% 0.76/0.99  thf('73', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.76/0.99          | (r2_hidden @ 
% 0.76/0.99             (k4_tarski @ (sk_B_1 @ (k1_relat_1 @ X0)) @ 
% 0.76/0.99              (sk_D_1 @ (sk_B_1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.76/0.99             X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['70', '72'])).
% 0.76/0.99  thf('74', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.99  thf('75', plain,
% 0.76/0.99      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.99  thf('76', plain, ((((sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['69', '75'])).
% 0.76/0.99  thf('77', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['46', '66'])).
% 0.76/0.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.99  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.99  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.76/0.99  thf('80', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_2)),
% 0.76/0.99      inference('demod', [status(thm)], ['68', '79'])).
% 0.76/0.99  thf(t5_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.76/0.99       ( ( ( ![D:$i]:
% 0.76/0.99             ( ( r2_hidden @ D @ A ) =>
% 0.76/0.99               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.76/0.99           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.76/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.99           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_4, axiom,
% 0.76/0.99    (![D:$i,C:$i,B:$i,A:$i]:
% 0.76/0.99     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.76/0.99       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.76/0.99  thf('81', plain,
% 0.76/0.99      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.99         ((zip_tseitin_1 @ X44 @ X45 @ X46 @ X47) | (r2_hidden @ X44 @ X47))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.76/0.99  thf('82', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.99  thf('83', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.99         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['81', '82'])).
% 0.76/0.99  thf('84', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_6, axiom,
% 0.76/0.99    (![C:$i,B:$i,A:$i]:
% 0.76/0.99     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.76/0.99       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_8, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.99       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.76/0.99           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.76/0.99         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 0.76/0.99  thf('85', plain,
% 0.76/0.99      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.76/0.99         (((k1_relat_1 @ X52) != (X51))
% 0.76/0.99          | ~ (zip_tseitin_1 @ (sk_D_3 @ X52 @ X53 @ X51) @ X52 @ X53 @ X51)
% 0.76/0.99          | (zip_tseitin_2 @ X52 @ X53 @ X51)
% 0.76/0.99          | ~ (v1_funct_1 @ X52)
% 0.76/0.99          | ~ (v1_relat_1 @ X52))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.76/0.99  thf('86', plain,
% 0.76/0.99      (![X52 : $i, X53 : $i]:
% 0.76/0.99         (~ (v1_relat_1 @ X52)
% 0.76/0.99          | ~ (v1_funct_1 @ X52)
% 0.76/0.99          | (zip_tseitin_2 @ X52 @ X53 @ (k1_relat_1 @ X52))
% 0.76/0.99          | ~ (zip_tseitin_1 @ (sk_D_3 @ X52 @ X53 @ (k1_relat_1 @ X52)) @ 
% 0.76/0.99               X52 @ X53 @ (k1_relat_1 @ X52)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['85'])).
% 0.76/0.99  thf('87', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (zip_tseitin_1 @ (sk_D_3 @ sk_C_1 @ X0 @ sk_A) @ sk_C_1 @ X0 @ 
% 0.76/0.99             (k1_relat_1 @ sk_C_1))
% 0.76/0.99          | (zip_tseitin_2 @ sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.99          | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['84', '86'])).
% 0.76/0.99  thf('88', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf('89', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('91', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.99  thf('92', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (zip_tseitin_1 @ (sk_D_3 @ sk_C_1 @ X0 @ sk_A) @ sk_C_1 @ X0 @ sk_A)
% 0.76/0.99          | (zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.76/0.99  thf('93', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (v1_xboole_0 @ sk_A) | (zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['83', '92'])).
% 0.76/0.99  thf('94', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['46', '66'])).
% 0.76/0.99  thf('95', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (v1_xboole_0 @ sk_A) | (zip_tseitin_2 @ k1_xboole_0 @ X0 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['93', '94'])).
% 0.76/0.99  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.76/0.99  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.99  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.76/0.99  thf('99', plain,
% 0.76/0.99      (![X0 : $i]: (zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.76/0.99      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.76/0.99  thf('100', plain,
% 0.76/0.99      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.99         ((v1_funct_2 @ X48 @ X50 @ X49) | ~ (zip_tseitin_2 @ X48 @ X49 @ X50))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.76/0.99  thf('101', plain,
% 0.76/0.99      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.76/0.99      inference('sup-', [status(thm)], ['99', '100'])).
% 0.76/0.99  thf('102', plain, ($false), inference('demod', [status(thm)], ['80', '101'])).
% 0.76/0.99  
% 0.76/0.99  % SZS output end Refutation
% 0.76/0.99  
% 0.76/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
