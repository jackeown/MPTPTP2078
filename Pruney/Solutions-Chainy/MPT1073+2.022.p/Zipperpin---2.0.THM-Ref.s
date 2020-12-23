%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e5awp0OmEG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:16 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 182 expanded)
%              Number of leaves         :   47 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  797 (1800 expanded)
%              Number of equality atoms :   47 (  87 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ X29 )
      | ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['9','12','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1 ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('25',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21
        = ( k2_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X21 @ X18 ) @ ( sk_C @ X21 @ X18 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X21 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v5_relat_1 @ X11 @ X13 )
      | ~ ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v5_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( v5_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( v5_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( v5_relat_1 @ sk_D_2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v5_relat_1 @ sk_D_2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ X25 @ X27 )
      | ~ ( v5_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['26','63'])).

thf('65',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['23','64'])).

thf('66',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['16','65'])).

thf('67',plain,(
    ! [X48: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['4','6'])).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ X29 )
      | ( X30
        = ( k1_funct_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('73',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['68','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e5awp0OmEG
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 232 iterations in 0.214s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.67  thf(t190_funct_2, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.46/0.67            ( ![E:$i]:
% 0.46/0.67              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.46/0.67               ( ![E:$i]:
% 0.46/0.67                 ( ( m1_subset_1 @ E @ B ) =>
% 0.46/0.67                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.46/0.67          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.67  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.67  thf(d5_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.67       ( ![C:$i]:
% 0.46/0.67         ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.67           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X20 @ X19)
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X20 @ X18) @ X20) @ X18)
% 0.46/0.67          | ((X19) != (k2_relat_1 @ X18)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X18 : $i, X20 : $i]:
% 0.46/0.67         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X20 @ X18) @ X20) @ X18)
% 0.46/0.67          | ~ (r2_hidden @ X20 @ (k2_relat_1 @ X18)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_A) @ sk_D_2)),
% 0.46/0.67      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.67  thf(t8_funct_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.67         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.67           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ X29)
% 0.46/0.67          | (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.46/0.67          | ~ (v1_funct_1 @ X29)
% 0.46/0.67          | ~ (v1_relat_1 @ X29))),
% 0.46/0.67      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_D_2)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_D_2)
% 0.46/0.67        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( v1_relat_1 @ C ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.67         ((v1_relat_1 @ X31)
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.67  thf('12', plain, ((v1_relat_1 @ sk_D_2)),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf('13', plain, ((v1_funct_1 @ sk_D_2)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '12', '13'])).
% 0.46/0.67  thf(t1_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.67  thf('17', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d1_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_1, axiom,
% 0.46/0.67    (![C:$i,B:$i,A:$i]:
% 0.46/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.46/0.67         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.46/0.67          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.46/0.67          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.46/0.67        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.46/0.67          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.46/0.67        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_4, axiom,
% 0.46/0.67    (![B:$i,A:$i]:
% 0.46/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.67  thf(zf_stmt_5, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.46/0.67          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.46/0.67          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 0.46/0.67        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X40 : $i, X41 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.67  thf(t113_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X7 : $i, X8 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.46/0.67      inference('sup+', [status(thm)], ['27', '29'])).
% 0.46/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.67  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X18 : $i, X21 : $i]:
% 0.46/0.67         (((X21) = (k2_relat_1 @ X18))
% 0.46/0.67          | (r2_hidden @ 
% 0.46/0.67             (k4_tarski @ (sk_D @ X21 @ X18) @ (sk_C @ X21 @ X18)) @ X18)
% 0.46/0.67          | (r2_hidden @ (sk_C @ X21 @ X18) @ X21))),
% 0.46/0.67      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.46/0.67  thf(d1_xboole_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.46/0.67          | ((X1) = (k2_relat_1 @ X0))
% 0.46/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X1)
% 0.46/0.67          | ((X0) = (k2_relat_1 @ X1))
% 0.46/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (![X0 : $i]: (((k1_xboole_0) = (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '36'])).
% 0.46/0.67  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf(d10_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('41', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.46/0.67      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.67  thf(d19_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ B ) =>
% 0.46/0.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      (![X14 : $i, X15 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.46/0.67          | (v5_relat_1 @ X14 @ X15)
% 0.46/0.67          | ~ (v1_relat_1 @ X14))),
% 0.46/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc6_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.46/0.67       ( ![C:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.46/0.67          | (v5_relat_1 @ X11 @ X13)
% 0.46/0.67          | ~ (v5_relat_1 @ X12 @ X13)
% 0.46/0.67          | ~ (v1_relat_1 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.46/0.67          | ~ (v5_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1) @ X0)
% 0.46/0.67          | (v5_relat_1 @ sk_D_2 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.67  thf(fc6_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v5_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1) @ X0)
% 0.46/0.67          | (v5_relat_1 @ sk_D_2 @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.46/0.67        | (v5_relat_1 @ sk_D_2 @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['43', '48'])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.67  thf('51', plain,
% 0.46/0.67      ((v5_relat_1 @ sk_D_2 @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.67  thf('52', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.67  thf(t202_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.46/0.67       ( ![C:$i]:
% 0.46/0.67         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X25 @ (k2_relat_1 @ X26))
% 0.46/0.67          | (r2_hidden @ X25 @ X27)
% 0.46/0.67          | ~ (v5_relat_1 @ X26 @ X27)
% 0.46/0.67          | ~ (v1_relat_1 @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ sk_D_2)
% 0.46/0.67          | ~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.46/0.67          | (r2_hidden @ sk_A @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.67  thf('55', plain, ((v1_relat_1 @ sk_D_2)),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_2 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['51', '56'])).
% 0.46/0.67  thf('58', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (~ (v1_xboole_0 @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.67  thf('60', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['39', '59'])).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ k1_xboole_0) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['30', '60'])).
% 0.46/0.67  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf('63', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 0.46/0.67      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.67  thf('64', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['26', '63'])).
% 0.46/0.67  thf('65', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 0.46/0.67      inference('demod', [status(thm)], ['23', '64'])).
% 0.46/0.67  thf('66', plain, ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '65'])).
% 0.46/0.67  thf('67', plain,
% 0.46/0.67      (![X48 : $i]:
% 0.46/0.67         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X48))
% 0.46/0.67          | ~ (m1_subset_1 @ X48 @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      (((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.67  thf('69', plain,
% 0.46/0.67      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_A) @ sk_D_2)),
% 0.46/0.67      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         (~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ X29)
% 0.46/0.67          | ((X30) = (k1_funct_1 @ X29 @ X28))
% 0.46/0.67          | ~ (v1_funct_1 @ X29)
% 0.46/0.67          | ~ (v1_relat_1 @ X29))),
% 0.46/0.67      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_D_2)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_D_2)
% 0.46/0.67        | ((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.67  thf('72', plain, ((v1_relat_1 @ sk_D_2)),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf('73', plain, ((v1_funct_1 @ sk_D_2)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('74', plain,
% 0.46/0.67      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.46/0.67      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.46/0.67  thf('75', plain, (((sk_A) != (sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['68', '74'])).
% 0.46/0.67  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
