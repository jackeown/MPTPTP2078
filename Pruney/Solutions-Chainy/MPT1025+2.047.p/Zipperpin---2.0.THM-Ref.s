%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9EdAhpi3g6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:49 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  134 (1212 expanded)
%              Number of leaves         :   44 ( 371 expanded)
%              Depth                    :   21
%              Number of atoms          :  936 (17064 expanded)
%              Number of equality atoms :   60 ( 707 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_2 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_1 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_1 @ X41 @ X42 )
      | ( zip_tseitin_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X23: $i,X24: $i] :
      ( ( X23
       != ( k9_relat_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X24 @ X20 @ X21 ) @ X24 @ X20 @ X21 )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( k9_relat_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X24 @ X20 @ X21 ) @ X24 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('39',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('41',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ X17 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('43',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X44: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X44 ) )
      | ~ ( r2_hidden @ X44 @ sk_C )
      | ~ ( m1_subset_1 @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k1_funct_1 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('48',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','50'])).

thf('52',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['21','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','50'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 != k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','50'])).

thf('61',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('67',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('69',plain,(
    ~ ( r1_tarski @ sk_D_2 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('74',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['52','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_1 @ X41 @ X42 )
      | ( zip_tseitin_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_1 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_1 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,(
    ! [X36: $i] :
      ( zip_tseitin_1 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['83'])).

thf('85',plain,(
    zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['14','86','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9EdAhpi3g6
% 0.16/0.36  % Computer   : n014.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 09:40:53 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 346 iterations in 0.392s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.87  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.68/0.87  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.68/0.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.68/0.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.87  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.68/0.87  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.68/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.87  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.68/0.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.87  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.68/0.87  thf(t116_funct_2, conjecture,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.68/0.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.87       ( ![E:$i]:
% 0.68/0.87         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.68/0.87              ( ![F:$i]:
% 0.68/0.87                ( ( m1_subset_1 @ F @ A ) =>
% 0.68/0.87                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.68/0.87                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.68/0.87            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.87          ( ![E:$i]:
% 0.68/0.87            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.68/0.87                 ( ![F:$i]:
% 0.68/0.87                   ( ( m1_subset_1 @ F @ A ) =>
% 0.68/0.87                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.68/0.87                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('1', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k7_relset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.87       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.68/0.87          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.68/0.87           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.87  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.68/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.87  thf(t143_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ C ) =>
% 0.68/0.87       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.68/0.87         ( ?[D:$i]:
% 0.68/0.87           ( ( r2_hidden @ D @ B ) & 
% 0.68/0.87             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.68/0.87             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.68/0.87          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.68/0.87          | ~ (v1_relat_1 @ X13))),
% 0.68/0.87      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ sk_D_2)
% 0.68/0.87        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(cc2_relat_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ A ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X6 : $i, X7 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.68/0.87          | (v1_relat_1 @ X6)
% 0.68/0.87          | ~ (v1_relat_1 @ X7))),
% 0.68/0.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.87  thf(fc6_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.68/0.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.87  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('demod', [status(thm)], ['6', '11'])).
% 0.68/0.87  thf(t7_ordinal1, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X27 : $i, X28 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.68/0.87  thf('14', plain,
% 0.68/0.87      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('15', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(d1_funct_2, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.87           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.68/0.87             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.87         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.87           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.68/0.87             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_1, axiom,
% 0.68/0.87    (![C:$i,B:$i,A:$i]:
% 0.68/0.87     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.68/0.87       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.68/0.87         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.68/0.87          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.68/0.87          | ~ (zip_tseitin_2 @ X40 @ X39 @ X38))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.68/0.87        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k1_relset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.68/0.87         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.68/0.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['18', '19'])).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.68/0.87        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.68/0.87      inference('demod', [status(thm)], ['17', '20'])).
% 0.68/0.87  thf(zf_stmt_2, axiom,
% 0.68/0.87    (![B:$i,A:$i]:
% 0.68/0.87     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.87       ( zip_tseitin_1 @ B @ A ) ))).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      (![X36 : $i, X37 : $i]:
% 0.68/0.87         ((zip_tseitin_1 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.87  thf('23', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.68/0.87  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.68/0.87  thf(zf_stmt_5, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.87       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.68/0.87         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.87           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.68/0.87             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.68/0.87  thf('24', plain,
% 0.68/0.87      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.68/0.87         (~ (zip_tseitin_1 @ X41 @ X42)
% 0.68/0.87          | (zip_tseitin_2 @ X43 @ X41 @ X42)
% 0.68/0.87          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.68/0.87        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.87  thf('26', plain,
% 0.68/0.87      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['22', '25'])).
% 0.68/0.87  thf('27', plain,
% 0.68/0.87      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.68/0.87        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.68/0.87      inference('demod', [status(thm)], ['17', '20'])).
% 0.68/0.87  thf('28', plain,
% 0.68/0.87      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.68/0.87  thf('29', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.68/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.87  thf(d12_funct_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.68/0.87       ( ![B:$i,C:$i]:
% 0.68/0.87         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.68/0.87           ( ![D:$i]:
% 0.68/0.87             ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.87               ( ?[E:$i]:
% 0.68/0.87                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.68/0.87                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.68/0.87  thf(zf_stmt_7, axiom,
% 0.68/0.87    (![E:$i,D:$i,B:$i,A:$i]:
% 0.68/0.87     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.68/0.87       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.68/0.87         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_8, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.87       ( ![B:$i,C:$i]:
% 0.68/0.87         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.68/0.87           ( ![D:$i]:
% 0.68/0.87             ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.87               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.68/0.87  thf('30', plain,
% 0.68/0.87      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i]:
% 0.68/0.87         (((X23) != (k9_relat_1 @ X21 @ X20))
% 0.68/0.87          | (zip_tseitin_0 @ (sk_E_1 @ X24 @ X20 @ X21) @ X24 @ X20 @ X21)
% 0.68/0.87          | ~ (r2_hidden @ X24 @ X23)
% 0.68/0.87          | ~ (v1_funct_1 @ X21)
% 0.68/0.87          | ~ (v1_relat_1 @ X21))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.68/0.87  thf('31', plain,
% 0.68/0.87      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X21)
% 0.68/0.87          | ~ (v1_funct_1 @ X21)
% 0.68/0.87          | ~ (r2_hidden @ X24 @ (k9_relat_1 @ X21 @ X20))
% 0.68/0.87          | (zip_tseitin_0 @ (sk_E_1 @ X24 @ X20 @ X21) @ X24 @ X20 @ X21))),
% 0.68/0.87      inference('simplify', [status(thm)], ['30'])).
% 0.68/0.87  thf('32', plain,
% 0.68/0.87      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.68/0.87         sk_D_2)
% 0.68/0.87        | ~ (v1_funct_1 @ sk_D_2)
% 0.68/0.87        | ~ (v1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['29', '31'])).
% 0.68/0.87  thf('33', plain, ((v1_funct_1 @ sk_D_2)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.87  thf('35', plain,
% 0.68/0.87      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.68/0.87        sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.68/0.87  thf('36', plain,
% 0.68/0.87      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.87         ((r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.68/0.87          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.68/0.87  thf('37', plain,
% 0.68/0.87      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['35', '36'])).
% 0.68/0.87  thf(t1_subset, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.68/0.87  thf('38', plain,
% 0.68/0.87      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.68/0.87      inference('cnf', [status(esa)], [t1_subset])).
% 0.68/0.87  thf('39', plain,
% 0.68/0.87      ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['37', '38'])).
% 0.68/0.87  thf('40', plain,
% 0.68/0.87      (((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.68/0.87        | ((sk_B) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['28', '39'])).
% 0.68/0.87  thf('41', plain,
% 0.68/0.87      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.68/0.87        sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.68/0.87  thf('42', plain,
% 0.68/0.87      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.87         ((r2_hidden @ X15 @ X17) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.68/0.87  thf('43', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.68/0.87      inference('sup-', [status(thm)], ['41', '42'])).
% 0.68/0.87  thf('44', plain,
% 0.68/0.87      (![X44 : $i]:
% 0.68/0.87         (((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X44))
% 0.68/0.87          | ~ (r2_hidden @ X44 @ sk_C)
% 0.68/0.87          | ~ (m1_subset_1 @ X44 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('45', plain,
% 0.68/0.87      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.68/0.87        | ((sk_E_2)
% 0.68/0.87            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.87  thf('46', plain,
% 0.68/0.87      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.68/0.87        sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.68/0.87  thf('47', plain,
% 0.68/0.87      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.87         (((X16) = (k1_funct_1 @ X14 @ X15))
% 0.68/0.87          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.68/0.87  thf('48', plain,
% 0.68/0.87      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.68/0.87  thf('49', plain,
% 0.68/0.87      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.68/0.87        | ((sk_E_2) != (sk_E_2)))),
% 0.68/0.87      inference('demod', [status(thm)], ['45', '48'])).
% 0.68/0.87  thf('50', plain,
% 0.68/0.87      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)),
% 0.68/0.87      inference('simplify', [status(thm)], ['49'])).
% 0.68/0.87  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.68/0.87      inference('clc', [status(thm)], ['40', '50'])).
% 0.68/0.87  thf('52', plain,
% 0.68/0.87      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.68/0.87        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.68/0.87      inference('demod', [status(thm)], ['21', '51'])).
% 0.68/0.87  thf('53', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 0.68/0.87      inference('clc', [status(thm)], ['40', '50'])).
% 0.68/0.87  thf('55', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.87  thf('56', plain,
% 0.68/0.87      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.68/0.87         (((X41) != (k1_xboole_0))
% 0.68/0.87          | ((X42) = (k1_xboole_0))
% 0.68/0.87          | ((X43) = (k1_xboole_0))
% 0.68/0.87          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.68/0.87          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.87  thf('57', plain,
% 0.68/0.87      (![X42 : $i, X43 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X43 @ 
% 0.68/0.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ k1_xboole_0)))
% 0.68/0.87          | ~ (v1_funct_2 @ X43 @ X42 @ k1_xboole_0)
% 0.68/0.87          | ((X43) = (k1_xboole_0))
% 0.68/0.87          | ((X42) = (k1_xboole_0)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['56'])).
% 0.68/0.87  thf('58', plain,
% 0.68/0.87      ((((sk_A) = (k1_xboole_0))
% 0.68/0.87        | ((sk_D_2) = (k1_xboole_0))
% 0.68/0.87        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['55', '57'])).
% 0.68/0.87  thf('59', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 0.68/0.87      inference('clc', [status(thm)], ['40', '50'])).
% 0.68/0.87  thf('61', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.68/0.87      inference('demod', [status(thm)], ['59', '60'])).
% 0.68/0.87  thf('62', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['58', '61'])).
% 0.68/0.87  thf('63', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.68/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.87  thf('64', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.68/0.87          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.68/0.87          | ~ (v1_relat_1 @ X13))),
% 0.68/0.87      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.68/0.87  thf('65', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ sk_D_2)
% 0.68/0.87        | (r2_hidden @ 
% 0.68/0.87           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['63', '64'])).
% 0.68/0.87  thf('66', plain, ((v1_relat_1 @ sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.87  thf('67', plain,
% 0.68/0.87      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.68/0.87        sk_D_2)),
% 0.68/0.87      inference('demod', [status(thm)], ['65', '66'])).
% 0.68/0.87  thf('68', plain,
% 0.68/0.87      (![X27 : $i, X28 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.68/0.87  thf('69', plain,
% 0.68/0.87      (~ (r1_tarski @ sk_D_2 @ 
% 0.68/0.87          (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2))),
% 0.68/0.87      inference('sup-', [status(thm)], ['67', '68'])).
% 0.68/0.87  thf('70', plain,
% 0.68/0.87      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.68/0.87           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2))
% 0.68/0.87        | ((sk_A) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['62', '69'])).
% 0.68/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.87  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.87  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['70', '71'])).
% 0.68/0.87  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['70', '71'])).
% 0.68/0.87  thf('74', plain,
% 0.68/0.87      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.68/0.87        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_2)))),
% 0.68/0.87      inference('demod', [status(thm)], ['52', '72', '73'])).
% 0.68/0.87  thf('75', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.87  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['70', '71'])).
% 0.68/0.87  thf('77', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D_2 @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['75', '76'])).
% 0.68/0.87  thf('78', plain,
% 0.68/0.87      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.68/0.87         (~ (zip_tseitin_1 @ X41 @ X42)
% 0.68/0.87          | (zip_tseitin_2 @ X43 @ X41 @ X42)
% 0.68/0.87          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.87  thf('79', plain,
% 0.68/0.87      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.68/0.87        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['77', '78'])).
% 0.68/0.87  thf('80', plain,
% 0.68/0.87      (![X36 : $i, X37 : $i]:
% 0.68/0.87         ((zip_tseitin_1 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.87  thf('81', plain,
% 0.68/0.87      (![X36 : $i, X37 : $i]:
% 0.68/0.87         ((zip_tseitin_1 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.87  thf('82', plain, (![X36 : $i]: (zip_tseitin_1 @ X36 @ k1_xboole_0)),
% 0.68/0.87      inference('simplify', [status(thm)], ['81'])).
% 0.68/0.87  thf('83', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((zip_tseitin_1 @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.68/0.87      inference('sup+', [status(thm)], ['80', '82'])).
% 0.68/0.87  thf('84', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ X0)),
% 0.68/0.87      inference('eq_fact', [status(thm)], ['83'])).
% 0.68/0.87  thf('85', plain, ((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)),
% 0.68/0.87      inference('demod', [status(thm)], ['79', '84'])).
% 0.68/0.87  thf('86', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.68/0.87      inference('demod', [status(thm)], ['74', '85'])).
% 0.68/0.87  thf('87', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.87  thf('88', plain, ($false),
% 0.68/0.87      inference('demod', [status(thm)], ['14', '86', '87'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
