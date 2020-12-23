%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QibwGbCzOe

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:43 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  144 (1293 expanded)
%              Number of leaves         :   47 ( 396 expanded)
%              Depth                    :   21
%              Number of atoms          : 1002 (17664 expanded)
%              Number of equality atoms :   60 ( 707 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1 ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_2 @ X48 @ X47 @ X46 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_1 @ X49 @ X50 )
      | ( zip_tseitin_2 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
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
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
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
    ! [X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ( X28
       != ( k9_relat_1 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X29 @ X25 @ X26 ) @ X29 @ X25 @ X26 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r2_hidden @ X29 @ ( k9_relat_1 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X29 @ X25 @ X26 ) @ X29 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 )
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
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','46'])).

thf('48',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X22 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('50',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X52: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X52 ) )
      | ~ ( r2_hidden @ X52 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X52 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X21
        = ( k1_funct_1 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('55',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','57'])).

thf('59',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['21','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','57'])).

thf('62',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 != k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','57'])).

thf('68',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('74',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('76',plain,(
    ~ ( r1_tarski @ sk_D_2 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ sk_E_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('81',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['59','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('84',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_1 @ X49 @ X50 )
      | ( zip_tseitin_2 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 )
      | ( X45 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    ! [X44: $i] :
      ( zip_tseitin_1 @ X44 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['90'])).

thf('92',plain,(
    zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['81','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['14','93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QibwGbCzOe
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.72/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.89  % Solved by: fo/fo7.sh
% 0.72/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.89  % done 422 iterations in 0.432s
% 0.72/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.89  % SZS output start Refutation
% 0.72/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.72/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.89  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.72/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.72/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.72/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.72/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.89  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.72/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.89  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.72/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.72/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.72/0.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.72/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.72/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.89  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.72/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.72/0.89  thf(t116_funct_2, conjecture,
% 0.72/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.72/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.89       ( ![E:$i]:
% 0.72/0.89         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.72/0.89              ( ![F:$i]:
% 0.72/0.89                ( ( m1_subset_1 @ F @ A ) =>
% 0.72/0.89                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.72/0.89                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.72/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.89        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.72/0.89            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.89          ( ![E:$i]:
% 0.72/0.89            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.72/0.89                 ( ![F:$i]:
% 0.72/0.89                   ( ( m1_subset_1 @ F @ A ) =>
% 0.72/0.89                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.72/0.89                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.72/0.89    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.72/0.89  thf('0', plain,
% 0.72/0.89      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C_1))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('1', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf(redefinition_k7_relset_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.72/0.89  thf('2', plain,
% 0.72/0.89      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.72/0.89         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.72/0.89          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.72/0.89  thf('3', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.72/0.89           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.89  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['0', '3'])).
% 0.72/0.89  thf(t143_relat_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( v1_relat_1 @ C ) =>
% 0.72/0.89       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.72/0.89         ( ?[D:$i]:
% 0.72/0.89           ( ( r2_hidden @ D @ B ) & 
% 0.72/0.89             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.72/0.89             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.72/0.89  thf('5', plain,
% 0.72/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.89         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.72/0.89          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 0.72/0.89          | ~ (v1_relat_1 @ X18))),
% 0.72/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.72/0.89  thf('6', plain,
% 0.72/0.89      ((~ (v1_relat_1 @ sk_D_2)
% 0.72/0.89        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ 
% 0.72/0.89           (k1_relat_1 @ sk_D_2)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.89  thf('7', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf(cc2_relat_1, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( ( v1_relat_1 @ A ) =>
% 0.72/0.89       ( ![B:$i]:
% 0.72/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.72/0.89  thf('8', plain,
% 0.72/0.89      (![X11 : $i, X12 : $i]:
% 0.72/0.89         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.72/0.89          | (v1_relat_1 @ X11)
% 0.72/0.89          | ~ (v1_relat_1 @ X12))),
% 0.72/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.72/0.89  thf('9', plain,
% 0.72/0.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.72/0.89  thf(fc6_relat_1, axiom,
% 0.72/0.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.72/0.89  thf('10', plain,
% 0.72/0.89      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.72/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.72/0.89  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.72/0.89  thf('12', plain,
% 0.72/0.89      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ (k1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('demod', [status(thm)], ['6', '11'])).
% 0.72/0.89  thf(t7_ordinal1, axiom,
% 0.72/0.89    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.89  thf('13', plain,
% 0.72/0.89      (![X32 : $i, X33 : $i]:
% 0.72/0.89         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.72/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.72/0.89  thf('14', plain,
% 0.72/0.89      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.72/0.89  thf('15', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf(d1_funct_2, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.72/0.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.72/0.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.72/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.72/0.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.72/0.89  thf(zf_stmt_1, axiom,
% 0.72/0.89    (![C:$i,B:$i,A:$i]:
% 0.72/0.89     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.72/0.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.72/0.89  thf('16', plain,
% 0.72/0.89      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.72/0.89         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.72/0.89          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.72/0.89          | ~ (zip_tseitin_2 @ X48 @ X47 @ X46))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.72/0.89  thf('17', plain,
% 0.72/0.89      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.72/0.89        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.72/0.89  thf('18', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf(redefinition_k1_relset_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.72/0.89  thf('19', plain,
% 0.72/0.89      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.72/0.89         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.72/0.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.72/0.89  thf('20', plain,
% 0.72/0.89      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.72/0.89  thf('21', plain,
% 0.72/0.89      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.72/0.89        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.72/0.89      inference('demod', [status(thm)], ['17', '20'])).
% 0.72/0.89  thf(zf_stmt_2, axiom,
% 0.72/0.89    (![B:$i,A:$i]:
% 0.72/0.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.89       ( zip_tseitin_1 @ B @ A ) ))).
% 0.72/0.89  thf('22', plain,
% 0.72/0.89      (![X44 : $i, X45 : $i]:
% 0.72/0.89         ((zip_tseitin_1 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.89  thf('23', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.72/0.89  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.72/0.89  thf(zf_stmt_5, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.89       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.72/0.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.72/0.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.72/0.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.72/0.89  thf('24', plain,
% 0.72/0.89      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.72/0.89         (~ (zip_tseitin_1 @ X49 @ X50)
% 0.72/0.89          | (zip_tseitin_2 @ X51 @ X49 @ X50)
% 0.72/0.89          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.72/0.89  thf('25', plain,
% 0.72/0.89      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.72/0.89        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.72/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.72/0.89  thf('26', plain,
% 0.72/0.89      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.72/0.89      inference('sup-', [status(thm)], ['22', '25'])).
% 0.72/0.89  thf('27', plain,
% 0.72/0.89      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.72/0.89        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.72/0.89      inference('demod', [status(thm)], ['17', '20'])).
% 0.72/0.89  thf('28', plain,
% 0.72/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.89  thf('29', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['0', '3'])).
% 0.72/0.89  thf(d12_funct_1, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.72/0.89       ( ![B:$i,C:$i]:
% 0.72/0.89         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.72/0.89           ( ![D:$i]:
% 0.72/0.89             ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.89               ( ?[E:$i]:
% 0.72/0.89                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.72/0.89                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.72/0.89  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.72/0.89  thf(zf_stmt_7, axiom,
% 0.72/0.89    (![E:$i,D:$i,B:$i,A:$i]:
% 0.72/0.89     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.72/0.89       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.72/0.89         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.72/0.89  thf(zf_stmt_8, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.72/0.89       ( ![B:$i,C:$i]:
% 0.72/0.89         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.72/0.89           ( ![D:$i]:
% 0.72/0.89             ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.89               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.72/0.89  thf('30', plain,
% 0.72/0.89      (![X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 0.72/0.89         (((X28) != (k9_relat_1 @ X26 @ X25))
% 0.72/0.89          | (zip_tseitin_0 @ (sk_E_1 @ X29 @ X25 @ X26) @ X29 @ X25 @ X26)
% 0.72/0.89          | ~ (r2_hidden @ X29 @ X28)
% 0.72/0.89          | ~ (v1_funct_1 @ X26)
% 0.72/0.89          | ~ (v1_relat_1 @ X26))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.72/0.89  thf('31', plain,
% 0.72/0.89      (![X25 : $i, X26 : $i, X29 : $i]:
% 0.72/0.89         (~ (v1_relat_1 @ X26)
% 0.72/0.89          | ~ (v1_funct_1 @ X26)
% 0.72/0.89          | ~ (r2_hidden @ X29 @ (k9_relat_1 @ X26 @ X25))
% 0.72/0.89          | (zip_tseitin_0 @ (sk_E_1 @ X29 @ X25 @ X26) @ X29 @ X25 @ X26))),
% 0.72/0.89      inference('simplify', [status(thm)], ['30'])).
% 0.72/0.89  thf('32', plain,
% 0.72/0.89      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 0.72/0.89         sk_C_1 @ sk_D_2)
% 0.72/0.89        | ~ (v1_funct_1 @ sk_D_2)
% 0.72/0.89        | ~ (v1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['29', '31'])).
% 0.72/0.89  thf('33', plain, ((v1_funct_1 @ sk_D_2)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.72/0.89  thf('35', plain,
% 0.72/0.89      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 0.72/0.89        sk_C_1 @ sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.72/0.89  thf('36', plain,
% 0.72/0.89      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.72/0.89         ((r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.72/0.89          | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.72/0.89  thf('37', plain,
% 0.72/0.89      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['35', '36'])).
% 0.72/0.89  thf(d3_tarski, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.72/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.72/0.89  thf('38', plain,
% 0.72/0.89      (![X1 : $i, X3 : $i]:
% 0.72/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.89  thf('39', plain,
% 0.72/0.89      (![X1 : $i, X3 : $i]:
% 0.72/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.72/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.89  thf('40', plain,
% 0.72/0.89      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.72/0.89  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.72/0.89      inference('simplify', [status(thm)], ['40'])).
% 0.72/0.89  thf(t3_subset, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.89  thf('42', plain,
% 0.72/0.89      (![X5 : $i, X7 : $i]:
% 0.72/0.89         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.72/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.72/0.89  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.72/0.89  thf(t4_subset, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.72/0.89       ( m1_subset_1 @ A @ C ) ))).
% 0.72/0.89  thf('44', plain,
% 0.72/0.89      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.72/0.89         (~ (r2_hidden @ X8 @ X9)
% 0.72/0.89          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.72/0.89          | (m1_subset_1 @ X8 @ X10))),
% 0.72/0.89      inference('cnf', [status(esa)], [t4_subset])).
% 0.72/0.89  thf('45', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.72/0.89  thf('46', plain,
% 0.72/0.89      ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ 
% 0.72/0.89        (k1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['37', '45'])).
% 0.72/0.89  thf('47', plain,
% 0.72/0.89      (((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)
% 0.72/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.72/0.89      inference('sup+', [status(thm)], ['28', '46'])).
% 0.72/0.89  thf('48', plain,
% 0.72/0.89      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 0.72/0.89        sk_C_1 @ sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.72/0.89  thf('49', plain,
% 0.72/0.89      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.72/0.89         ((r2_hidden @ X20 @ X22) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.72/0.89  thf('50', plain,
% 0.72/0.89      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_C_1)),
% 0.72/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.72/0.89  thf('51', plain,
% 0.72/0.89      (![X52 : $i]:
% 0.72/0.89         (((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X52))
% 0.72/0.89          | ~ (r2_hidden @ X52 @ sk_C_1)
% 0.72/0.89          | ~ (m1_subset_1 @ X52 @ sk_A))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('52', plain,
% 0.72/0.89      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)
% 0.72/0.89        | ((sk_E_2)
% 0.72/0.89            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['50', '51'])).
% 0.72/0.89  thf('53', plain,
% 0.72/0.89      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 0.72/0.89        sk_C_1 @ sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.72/0.89  thf('54', plain,
% 0.72/0.89      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.72/0.89         (((X21) = (k1_funct_1 @ X19 @ X20))
% 0.72/0.89          | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.72/0.89  thf('55', plain,
% 0.72/0.89      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['53', '54'])).
% 0.72/0.89  thf('56', plain,
% 0.72/0.89      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)
% 0.72/0.89        | ((sk_E_2) != (sk_E_2)))),
% 0.72/0.89      inference('demod', [status(thm)], ['52', '55'])).
% 0.72/0.89  thf('57', plain,
% 0.72/0.89      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)),
% 0.72/0.89      inference('simplify', [status(thm)], ['56'])).
% 0.72/0.89  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.72/0.89      inference('clc', [status(thm)], ['47', '57'])).
% 0.72/0.89  thf('59', plain,
% 0.72/0.89      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.72/0.89        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.72/0.89      inference('demod', [status(thm)], ['21', '58'])).
% 0.72/0.89  thf('60', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('61', plain, (((sk_B) = (k1_xboole_0))),
% 0.72/0.89      inference('clc', [status(thm)], ['47', '57'])).
% 0.72/0.89  thf('62', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.72/0.89      inference('demod', [status(thm)], ['60', '61'])).
% 0.72/0.89  thf('63', plain,
% 0.72/0.89      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.72/0.89         (((X49) != (k1_xboole_0))
% 0.72/0.89          | ((X50) = (k1_xboole_0))
% 0.72/0.89          | ((X51) = (k1_xboole_0))
% 0.72/0.89          | ~ (v1_funct_2 @ X51 @ X50 @ X49)
% 0.72/0.89          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.72/0.89  thf('64', plain,
% 0.72/0.89      (![X50 : $i, X51 : $i]:
% 0.72/0.89         (~ (m1_subset_1 @ X51 @ 
% 0.72/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ k1_xboole_0)))
% 0.72/0.89          | ~ (v1_funct_2 @ X51 @ X50 @ k1_xboole_0)
% 0.72/0.89          | ((X51) = (k1_xboole_0))
% 0.72/0.89          | ((X50) = (k1_xboole_0)))),
% 0.72/0.89      inference('simplify', [status(thm)], ['63'])).
% 0.72/0.89  thf('65', plain,
% 0.72/0.89      ((((sk_A) = (k1_xboole_0))
% 0.72/0.89        | ((sk_D_2) = (k1_xboole_0))
% 0.72/0.89        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['62', '64'])).
% 0.72/0.89  thf('66', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 0.72/0.89      inference('clc', [status(thm)], ['47', '57'])).
% 0.72/0.89  thf('68', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.72/0.89      inference('demod', [status(thm)], ['66', '67'])).
% 0.72/0.89  thf('69', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.72/0.89      inference('demod', [status(thm)], ['65', '68'])).
% 0.72/0.89  thf('70', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['0', '3'])).
% 0.72/0.89  thf('71', plain,
% 0.72/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.89         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.72/0.89          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 0.72/0.89          | ~ (v1_relat_1 @ X18))),
% 0.72/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.72/0.89  thf('72', plain,
% 0.72/0.89      ((~ (v1_relat_1 @ sk_D_2)
% 0.72/0.89        | (r2_hidden @ 
% 0.72/0.89           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['70', '71'])).
% 0.72/0.89  thf('73', plain, ((v1_relat_1 @ sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.72/0.89  thf('74', plain,
% 0.72/0.89      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ sk_E_2) @ 
% 0.72/0.89        sk_D_2)),
% 0.72/0.89      inference('demod', [status(thm)], ['72', '73'])).
% 0.72/0.89  thf('75', plain,
% 0.72/0.89      (![X32 : $i, X33 : $i]:
% 0.72/0.89         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.72/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.72/0.89  thf('76', plain,
% 0.72/0.89      (~ (r1_tarski @ sk_D_2 @ 
% 0.72/0.89          (k4_tarski @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ sk_E_2))),
% 0.72/0.89      inference('sup-', [status(thm)], ['74', '75'])).
% 0.72/0.89  thf('77', plain,
% 0.72/0.89      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.72/0.89           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ sk_E_2))
% 0.72/0.89        | ((sk_A) = (k1_xboole_0)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['69', '76'])).
% 0.72/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.72/0.89  thf('78', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.72/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.72/0.89  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 0.72/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.72/0.89  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.72/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.72/0.89  thf('81', plain,
% 0.72/0.89      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.72/0.89        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_2)))),
% 0.72/0.89      inference('demod', [status(thm)], ['59', '79', '80'])).
% 0.72/0.89  thf('82', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.72/0.89      inference('demod', [status(thm)], ['60', '61'])).
% 0.72/0.89  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 0.72/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.72/0.89  thf('84', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_D_2 @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.72/0.89      inference('demod', [status(thm)], ['82', '83'])).
% 0.72/0.89  thf('85', plain,
% 0.72/0.89      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.72/0.89         (~ (zip_tseitin_1 @ X49 @ X50)
% 0.72/0.89          | (zip_tseitin_2 @ X51 @ X49 @ X50)
% 0.72/0.89          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.72/0.89  thf('86', plain,
% 0.72/0.89      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.72/0.89        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['84', '85'])).
% 0.72/0.89  thf('87', plain,
% 0.72/0.89      (![X44 : $i, X45 : $i]:
% 0.72/0.89         ((zip_tseitin_1 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.89  thf('88', plain,
% 0.72/0.89      (![X44 : $i, X45 : $i]:
% 0.72/0.89         ((zip_tseitin_1 @ X44 @ X45) | ((X45) != (k1_xboole_0)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.89  thf('89', plain, (![X44 : $i]: (zip_tseitin_1 @ X44 @ k1_xboole_0)),
% 0.72/0.89      inference('simplify', [status(thm)], ['88'])).
% 0.72/0.89  thf('90', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         ((zip_tseitin_1 @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.72/0.89      inference('sup+', [status(thm)], ['87', '89'])).
% 0.72/0.89  thf('91', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ X0)),
% 0.72/0.89      inference('eq_fact', [status(thm)], ['90'])).
% 0.72/0.89  thf('92', plain, ((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)),
% 0.72/0.89      inference('demod', [status(thm)], ['86', '91'])).
% 0.72/0.89  thf('93', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.72/0.89      inference('demod', [status(thm)], ['81', '92'])).
% 0.72/0.89  thf('94', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.72/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.72/0.89  thf('95', plain, ($false),
% 0.72/0.89      inference('demod', [status(thm)], ['14', '93', '94'])).
% 0.72/0.89  
% 0.72/0.89  % SZS output end Refutation
% 0.72/0.89  
% 0.72/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
