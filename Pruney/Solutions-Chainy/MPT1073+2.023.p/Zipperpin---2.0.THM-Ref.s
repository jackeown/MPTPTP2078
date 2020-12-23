%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBaRmdzgnU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:16 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 165 expanded)
%              Number of leaves         :   42 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  730 (1805 expanded)
%              Number of equality atoms :   42 (  81 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['9','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('18',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ ( sk_F @ X38 @ X39 @ X40 ) @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_F @ sk_C @ sk_B_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_B_1 @ ( sk_B @ sk_D_1 ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ( X44
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X19 @ X20 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X50: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['9','12'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['48','54'])).

thf('56',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['15','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBaRmdzgnU
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 269 iterations in 0.383s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.60/0.84  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.84  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.60/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.84  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(t190_funct_2, conjecture,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.60/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.84       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.60/0.84            ( ![E:$i]:
% 0.60/0.84              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.60/0.84            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.84          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.60/0.84               ( ![E:$i]:
% 0.60/0.84                 ( ( m1_subset_1 @ E @ B ) =>
% 0.60/0.84                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.60/0.84  thf('0', plain,
% 0.60/0.84      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('1', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.84  thf('2', plain,
% 0.60/0.84      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.84         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 0.60/0.84          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.84  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.84  thf(t146_relat_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ A ) =>
% 0.60/0.84       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X22 : $i]:
% 0.60/0.84         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 0.60/0.84          | ~ (v1_relat_1 @ X22))),
% 0.60/0.84      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.60/0.84  thf(t143_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ C ) =>
% 0.60/0.84       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.60/0.84         ( ?[D:$i]:
% 0.60/0.84           ( ( r2_hidden @ D @ B ) & 
% 0.60/0.84             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.60/0.84             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.60/0.84  thf('6', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.60/0.84          | (r2_hidden @ (k4_tarski @ (sk_D @ X21 @ X19 @ X20) @ X20) @ X21)
% 0.60/0.84          | ~ (v1_relat_1 @ X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.84  thf('7', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | (r2_hidden @ 
% 0.60/0.84             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((r2_hidden @ 
% 0.60/0.84           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.84        | (r2_hidden @ 
% 0.60/0.84           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.60/0.84           sk_D_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['4', '8'])).
% 0.60/0.84  thf('10', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc1_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( v1_relat_1 @ C ) ))).
% 0.60/0.84  thf('11', plain,
% 0.60/0.84      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.84         ((v1_relat_1 @ X29)
% 0.60/0.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.84  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('13', plain,
% 0.60/0.84      ((r2_hidden @ 
% 0.60/0.84        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.60/0.84        sk_D_1)),
% 0.60/0.84      inference('demod', [status(thm)], ['9', '12'])).
% 0.60/0.84  thf(d1_xboole_0, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.84  thf('15', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.84  thf('16', plain,
% 0.60/0.84      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.60/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t6_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.60/0.84       ( ~( ( r2_hidden @ A @ D ) & 
% 0.60/0.84            ( ![E:$i,F:$i]:
% 0.60/0.84              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.60/0.84                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.60/0.84         ((r2_hidden @ (sk_F @ X38 @ X39 @ X40) @ X38)
% 0.60/0.84          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.60/0.84          | ~ (r2_hidden @ X40 @ X41))),
% 0.60/0.84      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.60/0.84          | (r2_hidden @ (sk_F @ sk_C @ sk_B_1 @ X0) @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      (((v1_xboole_0 @ sk_D_1)
% 0.60/0.84        | (r2_hidden @ (sk_F @ sk_C @ sk_B_1 @ (sk_B @ sk_D_1)) @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['16', '19'])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.84  thf('22', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.84  thf(d1_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.84           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.84             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.84           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.84             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_1, axiom,
% 0.60/0.84    (![B:$i,A:$i]:
% 0.60/0.84     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.84       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.84  thf('23', plain,
% 0.60/0.84      (![X42 : $i, X43 : $i]:
% 0.60/0.84         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.84  thf('24', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.84  thf(zf_stmt_3, axiom,
% 0.60/0.84    (![C:$i,B:$i,A:$i]:
% 0.60/0.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.84       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.84  thf(zf_stmt_5, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.84         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.84           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.84             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.60/0.84         (~ (zip_tseitin_0 @ X47 @ X48)
% 0.60/0.84          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 0.60/0.84          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.60/0.84        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['23', '26'])).
% 0.60/0.84  thf('28', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.60/0.84         (~ (v1_funct_2 @ X46 @ X44 @ X45)
% 0.60/0.84          | ((X44) = (k1_relset_1 @ X44 @ X45 @ X46))
% 0.60/0.84          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.60/0.84        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.84         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.60/0.84          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.60/0.84        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.60/0.84      inference('demod', [status(thm)], ['30', '33'])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      ((((sk_C) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['27', '34'])).
% 0.60/0.84  thf('36', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      (![X22 : $i]:
% 0.60/0.84         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 0.60/0.84          | ~ (v1_relat_1 @ X22))),
% 0.60/0.84      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.60/0.84          | (r2_hidden @ (sk_D @ X21 @ X19 @ X20) @ (k1_relat_1 @ X21))
% 0.60/0.84          | ~ (v1_relat_1 @ X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.60/0.84             (k1_relat_1 @ X0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['39'])).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.84        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.60/0.84           (k1_relat_1 @ sk_D_1)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['36', '40'])).
% 0.60/0.84  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.60/0.84        (k1_relat_1 @ sk_D_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['41', '42'])).
% 0.60/0.84  thf(t1_subset, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.60/0.84  thf('44', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.60/0.84      inference('cnf', [status(esa)], [t1_subset])).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.60/0.84        (k1_relat_1 @ sk_D_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.84  thf('46', plain,
% 0.60/0.84      (((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_B_1)
% 0.60/0.84        | ((sk_C) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['35', '45'])).
% 0.60/0.84  thf('47', plain,
% 0.60/0.84      (![X50 : $i]:
% 0.60/0.84         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X50))
% 0.60/0.84          | ~ (m1_subset_1 @ X50 @ sk_B_1))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      ((((sk_C) = (k1_xboole_0))
% 0.60/0.84        | ((sk_A)
% 0.60/0.84            != (k1_funct_1 @ sk_D_1 @ 
% 0.60/0.84                (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      ((r2_hidden @ 
% 0.60/0.84        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.60/0.84        sk_D_1)),
% 0.60/0.84      inference('demod', [status(thm)], ['9', '12'])).
% 0.60/0.84  thf(t8_funct_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.60/0.84       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.60/0.84         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.60/0.84           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.60/0.84  thf('50', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.84         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.60/0.84          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.60/0.84          | ~ (v1_funct_1 @ X27)
% 0.60/0.84          | ~ (v1_relat_1 @ X27))),
% 0.60/0.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.84  thf('51', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.60/0.84        | ~ (v1_funct_1 @ sk_D_1)
% 0.60/0.84        | ((sk_A)
% 0.60/0.84            = (k1_funct_1 @ sk_D_1 @ 
% 0.60/0.84               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['49', '50'])).
% 0.60/0.84  thf('52', plain, ((v1_relat_1 @ sk_D_1)),
% 0.60/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('53', plain, ((v1_funct_1 @ sk_D_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('54', plain,
% 0.60/0.84      (((sk_A)
% 0.60/0.84         = (k1_funct_1 @ sk_D_1 @ 
% 0.60/0.84            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.60/0.84  thf('55', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['48', '54'])).
% 0.60/0.84  thf('56', plain, (((sk_C) = (k1_xboole_0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['55'])).
% 0.60/0.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.84  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.84  thf('58', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.60/0.84      inference('demod', [status(thm)], ['22', '56', '57'])).
% 0.60/0.84  thf('59', plain, ($false), inference('demod', [status(thm)], ['15', '58'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
