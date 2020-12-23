%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EmerDmYtnh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:40 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  154 (1524 expanded)
%              Number of leaves         :   44 ( 464 expanded)
%              Depth                    :   21
%              Number of atoms          : 1047 (21710 expanded)
%              Number of equality atoms :   67 ( 929 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
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
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_2 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_1 @ X39 @ X40 )
      | ( zip_tseitin_2 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
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

thf('38',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_A )
      | ~ ( r2_hidden @ X42 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k1_funct_1 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('43',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ X17 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('46',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('48',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['21','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 != k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('58',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('71',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['49','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('74',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_1 @ X39 @ X40 )
      | ( zip_tseitin_2 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X34 @ X35 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    ! [X34: $i] :
      ( zip_tseitin_1 @ X34 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_1 @ sk_A @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_1 @ sk_A @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ( zip_tseitin_1 @ sk_A @ X1 ) ) ),
    inference(clc,[status(thm)],['92','95'])).

thf('97',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('104',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['76','104'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['71','105'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['14','106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EmerDmYtnh
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.20  % Solved by: fo/fo7.sh
% 0.97/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.20  % done 346 iterations in 0.744s
% 0.97/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.20  % SZS output start Refutation
% 0.97/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.97/1.20  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.97/1.20  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.97/1.20  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.97/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.97/1.20  thf(sk_C_type, type, sk_C: $i).
% 0.97/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.97/1.20  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.97/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.97/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.97/1.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.97/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.97/1.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.97/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.97/1.20  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.97/1.20  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.97/1.20  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.97/1.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.97/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.97/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.97/1.20  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.97/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.20  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.97/1.20  thf(sk_B_type, type, sk_B: $i > $i).
% 0.97/1.20  thf(t115_funct_2, conjecture,
% 0.97/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.20     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.97/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.97/1.20       ( ![E:$i]:
% 0.97/1.20         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.97/1.20              ( ![F:$i]:
% 0.97/1.20                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.97/1.20                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.97/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.20    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.20        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.97/1.20            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.97/1.20          ( ![E:$i]:
% 0.97/1.20            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.97/1.20                 ( ![F:$i]:
% 0.97/1.20                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.97/1.20                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.97/1.20    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.97/1.20  thf('0', plain,
% 0.97/1.20      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('1', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(redefinition_k7_relset_1, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.20       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.97/1.20  thf('2', plain,
% 0.97/1.20      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.97/1.20          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.97/1.20      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.97/1.20  thf('3', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.97/1.20           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['1', '2'])).
% 0.97/1.20  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('demod', [status(thm)], ['0', '3'])).
% 0.97/1.20  thf(t143_relat_1, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i]:
% 0.97/1.20     ( ( v1_relat_1 @ C ) =>
% 0.97/1.20       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.97/1.20         ( ?[D:$i]:
% 0.97/1.20           ( ( r2_hidden @ D @ B ) & 
% 0.97/1.20             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.97/1.20             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.97/1.20  thf('5', plain,
% 0.97/1.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.97/1.20         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.97/1.20          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.97/1.20          | ~ (v1_relat_1 @ X13))),
% 0.97/1.20      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.97/1.20  thf('6', plain,
% 0.97/1.20      ((~ (v1_relat_1 @ sk_D_2)
% 0.97/1.20        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['4', '5'])).
% 0.97/1.20  thf('7', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(cc2_relat_1, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( v1_relat_1 @ A ) =>
% 0.97/1.20       ( ![B:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.97/1.20  thf('8', plain,
% 0.97/1.20      (![X6 : $i, X7 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.97/1.20          | (v1_relat_1 @ X6)
% 0.97/1.20          | ~ (v1_relat_1 @ X7))),
% 0.97/1.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.97/1.20  thf('9', plain,
% 0.97/1.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 0.97/1.20  thf(fc6_relat_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.97/1.20  thf('10', plain,
% 0.97/1.20      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.97/1.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.97/1.20  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['9', '10'])).
% 0.97/1.20  thf('12', plain,
% 0.97/1.20      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('demod', [status(thm)], ['6', '11'])).
% 0.97/1.20  thf(d1_xboole_0, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.97/1.20  thf('13', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.97/1.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.97/1.20  thf('14', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['12', '13'])).
% 0.97/1.20  thf('15', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(d1_funct_2, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.20       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.97/1.20           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.97/1.20             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.97/1.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.97/1.20           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.97/1.20             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.97/1.20  thf(zf_stmt_1, axiom,
% 0.97/1.20    (![C:$i,B:$i,A:$i]:
% 0.97/1.20     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.97/1.20       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.97/1.20  thf('16', plain,
% 0.97/1.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.97/1.20         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.97/1.20          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.97/1.20          | ~ (zip_tseitin_2 @ X38 @ X37 @ X36))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.97/1.20  thf('17', plain,
% 0.97/1.20      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.97/1.20        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 0.97/1.20  thf('18', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(redefinition_k1_relset_1, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.97/1.20  thf('19', plain,
% 0.97/1.20      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.97/1.20         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.97/1.20          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.97/1.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.97/1.20  thf('20', plain,
% 0.97/1.20      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 0.97/1.20  thf('21', plain,
% 0.97/1.20      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.97/1.20        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('demod', [status(thm)], ['17', '20'])).
% 0.97/1.20  thf(zf_stmt_2, axiom,
% 0.97/1.20    (![B:$i,A:$i]:
% 0.97/1.20     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.97/1.20       ( zip_tseitin_1 @ B @ A ) ))).
% 0.97/1.20  thf('22', plain,
% 0.97/1.20      (![X34 : $i, X35 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.20  thf('23', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.97/1.20  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.97/1.20  thf(zf_stmt_5, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.20       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.97/1.20         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.97/1.20           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.97/1.20             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.97/1.20  thf('24', plain,
% 0.97/1.20      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.97/1.20         (~ (zip_tseitin_1 @ X39 @ X40)
% 0.97/1.20          | (zip_tseitin_2 @ X41 @ X39 @ X40)
% 0.97/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.97/1.20  thf('25', plain,
% 0.97/1.20      (((zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.97/1.20        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 0.97/1.20  thf('26', plain,
% 0.97/1.20      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['22', '25'])).
% 0.97/1.20  thf('27', plain,
% 0.97/1.20      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.97/1.20        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('demod', [status(thm)], ['17', '20'])).
% 0.97/1.20  thf('28', plain,
% 0.97/1.20      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['26', '27'])).
% 0.97/1.20  thf('29', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('demod', [status(thm)], ['0', '3'])).
% 0.97/1.20  thf(d12_funct_1, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.97/1.20       ( ![B:$i,C:$i]:
% 0.97/1.20         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.97/1.20           ( ![D:$i]:
% 0.97/1.20             ( ( r2_hidden @ D @ C ) <=>
% 0.97/1.20               ( ?[E:$i]:
% 0.97/1.20                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.97/1.20                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.97/1.20  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.97/1.20  thf(zf_stmt_7, axiom,
% 0.97/1.20    (![E:$i,D:$i,B:$i,A:$i]:
% 0.97/1.20     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.97/1.20       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.97/1.20         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.97/1.20  thf(zf_stmt_8, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.97/1.20       ( ![B:$i,C:$i]:
% 0.97/1.20         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.97/1.20           ( ![D:$i]:
% 0.97/1.20             ( ( r2_hidden @ D @ C ) <=>
% 0.97/1.20               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.97/1.20  thf('30', plain,
% 0.97/1.20      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i]:
% 0.97/1.20         (((X23) != (k9_relat_1 @ X21 @ X20))
% 0.97/1.20          | (zip_tseitin_0 @ (sk_E_1 @ X24 @ X20 @ X21) @ X24 @ X20 @ X21)
% 0.97/1.20          | ~ (r2_hidden @ X24 @ X23)
% 0.97/1.20          | ~ (v1_funct_1 @ X21)
% 0.97/1.20          | ~ (v1_relat_1 @ X21))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.97/1.20  thf('31', plain,
% 0.97/1.20      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.97/1.20         (~ (v1_relat_1 @ X21)
% 0.97/1.20          | ~ (v1_funct_1 @ X21)
% 0.97/1.20          | ~ (r2_hidden @ X24 @ (k9_relat_1 @ X21 @ X20))
% 0.97/1.20          | (zip_tseitin_0 @ (sk_E_1 @ X24 @ X20 @ X21) @ X24 @ X20 @ X21))),
% 0.97/1.20      inference('simplify', [status(thm)], ['30'])).
% 0.97/1.20  thf('32', plain,
% 0.97/1.20      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.97/1.20         sk_D_2)
% 0.97/1.20        | ~ (v1_funct_1 @ sk_D_2)
% 0.97/1.20        | ~ (v1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['29', '31'])).
% 0.97/1.20  thf('33', plain, ((v1_funct_1 @ sk_D_2)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['9', '10'])).
% 0.97/1.20  thf('35', plain,
% 0.97/1.20      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.97/1.20        sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.97/1.20  thf('36', plain,
% 0.97/1.20      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.97/1.20         ((r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.97/1.20          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.97/1.20  thf('37', plain,
% 0.97/1.20      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 0.97/1.20  thf('38', plain,
% 0.97/1.20      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.97/1.20        | ((sk_B_1) = (k1_xboole_0)))),
% 0.97/1.20      inference('sup+', [status(thm)], ['28', '37'])).
% 0.97/1.20  thf('39', plain,
% 0.97/1.20      (![X42 : $i]:
% 0.97/1.20         (~ (r2_hidden @ X42 @ sk_A)
% 0.97/1.20          | ~ (r2_hidden @ X42 @ sk_C)
% 0.97/1.20          | ((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X42)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('40', plain,
% 0.97/1.20      ((((sk_B_1) = (k1_xboole_0))
% 0.97/1.20        | ((sk_E_2)
% 0.97/1.20            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))
% 0.97/1.20        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C))),
% 0.97/1.20      inference('sup-', [status(thm)], ['38', '39'])).
% 0.97/1.20  thf('41', plain,
% 0.97/1.20      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.97/1.20        sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.97/1.20  thf('42', plain,
% 0.97/1.20      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.97/1.20         (((X16) = (k1_funct_1 @ X14 @ X15))
% 0.97/1.20          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.97/1.20  thf('43', plain,
% 0.97/1.20      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['41', '42'])).
% 0.97/1.20  thf('44', plain,
% 0.97/1.20      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.97/1.20        sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.97/1.20  thf('45', plain,
% 0.97/1.20      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.97/1.20         ((r2_hidden @ X15 @ X17) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.97/1.20  thf('46', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.97/1.20      inference('sup-', [status(thm)], ['44', '45'])).
% 0.97/1.20  thf('47', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_E_2) != (sk_E_2)))),
% 0.97/1.20      inference('demod', [status(thm)], ['40', '43', '46'])).
% 0.97/1.20  thf('48', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.97/1.20      inference('simplify', [status(thm)], ['47'])).
% 0.97/1.20  thf('49', plain,
% 0.97/1.20      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.97/1.20        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('demod', [status(thm)], ['21', '48'])).
% 0.97/1.20  thf('50', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.97/1.20      inference('simplify', [status(thm)], ['47'])).
% 0.97/1.20  thf('52', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ 
% 0.97/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.97/1.20      inference('demod', [status(thm)], ['50', '51'])).
% 0.97/1.20  thf('53', plain,
% 0.97/1.20      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.97/1.20         (((X39) != (k1_xboole_0))
% 0.97/1.20          | ((X40) = (k1_xboole_0))
% 0.97/1.20          | ((X41) = (k1_xboole_0))
% 0.97/1.20          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.97/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.97/1.20  thf('54', plain,
% 0.97/1.20      (![X40 : $i, X41 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X41 @ 
% 0.97/1.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ k1_xboole_0)))
% 0.97/1.20          | ~ (v1_funct_2 @ X41 @ X40 @ k1_xboole_0)
% 0.97/1.20          | ((X41) = (k1_xboole_0))
% 0.97/1.20          | ((X40) = (k1_xboole_0)))),
% 0.97/1.20      inference('simplify', [status(thm)], ['53'])).
% 0.97/1.20  thf('55', plain,
% 0.97/1.20      ((((sk_A) = (k1_xboole_0))
% 0.97/1.20        | ((sk_D_2) = (k1_xboole_0))
% 0.97/1.20        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['52', '54'])).
% 0.97/1.20  thf('56', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('57', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.97/1.20      inference('simplify', [status(thm)], ['47'])).
% 0.97/1.20  thf('58', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.97/1.20      inference('demod', [status(thm)], ['56', '57'])).
% 0.97/1.20  thf('59', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.97/1.20      inference('demod', [status(thm)], ['55', '58'])).
% 0.97/1.20  thf('60', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('demod', [status(thm)], ['0', '3'])).
% 0.97/1.20  thf('61', plain,
% 0.97/1.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.97/1.20         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.97/1.20          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.97/1.20          | ~ (v1_relat_1 @ X13))),
% 0.97/1.20      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.97/1.20  thf('62', plain,
% 0.97/1.20      ((~ (v1_relat_1 @ sk_D_2)
% 0.97/1.20        | (r2_hidden @ 
% 0.97/1.20           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['60', '61'])).
% 0.97/1.20  thf('63', plain, ((v1_relat_1 @ sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['9', '10'])).
% 0.97/1.20  thf('64', plain,
% 0.97/1.20      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.97/1.20        sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['62', '63'])).
% 0.97/1.20  thf('65', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.97/1.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.97/1.20  thf('66', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.97/1.20      inference('sup-', [status(thm)], ['64', '65'])).
% 0.97/1.20  thf('67', plain,
% 0.97/1.20      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['59', '66'])).
% 0.97/1.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.97/1.20  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.97/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.97/1.20  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.97/1.20      inference('demod', [status(thm)], ['67', '68'])).
% 0.97/1.20  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.97/1.20      inference('demod', [status(thm)], ['67', '68'])).
% 0.97/1.20  thf('71', plain,
% 0.97/1.20      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.97/1.20        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('demod', [status(thm)], ['49', '69', '70'])).
% 0.97/1.20  thf('72', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ 
% 0.97/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.97/1.20      inference('demod', [status(thm)], ['50', '51'])).
% 0.97/1.20  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.97/1.20      inference('demod', [status(thm)], ['67', '68'])).
% 0.97/1.20  thf('74', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D_2 @ 
% 0.97/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.97/1.20      inference('demod', [status(thm)], ['72', '73'])).
% 0.97/1.20  thf('75', plain,
% 0.97/1.20      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.97/1.20         (~ (zip_tseitin_1 @ X39 @ X40)
% 0.97/1.20          | (zip_tseitin_2 @ X41 @ X39 @ X40)
% 0.97/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.97/1.20  thf('76', plain,
% 0.97/1.20      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.97/1.20        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['74', '75'])).
% 0.97/1.20  thf('77', plain,
% 0.97/1.20      (![X34 : $i, X35 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.20  thf('78', plain,
% 0.97/1.20      (![X34 : $i, X35 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ X34 @ X35) | ((X35) != (k1_xboole_0)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.20  thf('79', plain, (![X34 : $i]: (zip_tseitin_1 @ X34 @ k1_xboole_0)),
% 0.97/1.20      inference('simplify', [status(thm)], ['78'])).
% 0.97/1.20  thf('80', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.97/1.20      inference('sup+', [status(thm)], ['77', '79'])).
% 0.97/1.20  thf('81', plain,
% 0.97/1.20      (((zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.97/1.20        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 0.97/1.20  thf('82', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ sk_A @ X0)
% 0.97/1.20          | (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['80', '81'])).
% 0.97/1.20  thf('83', plain,
% 0.97/1.20      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.97/1.20        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('demod', [status(thm)], ['17', '20'])).
% 0.97/1.20  thf('84', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['82', '83'])).
% 0.97/1.20  thf('85', plain,
% 0.97/1.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.97/1.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.97/1.20  thf('86', plain,
% 0.97/1.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.97/1.20         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.97/1.20          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.97/1.20          | ~ (v1_relat_1 @ X13))),
% 0.97/1.20      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.97/1.20  thf('87', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]:
% 0.97/1.20         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.97/1.20          | ~ (v1_relat_1 @ X1)
% 0.97/1.20          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.97/1.20             (k1_relat_1 @ X1)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['85', '86'])).
% 0.97/1.20  thf('88', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.97/1.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.97/1.20  thf('89', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]:
% 0.97/1.20         (~ (v1_relat_1 @ X0)
% 0.97/1.20          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.97/1.20          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 0.97/1.20  thf('90', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]:
% 0.97/1.20         (~ (v1_xboole_0 @ sk_A)
% 0.97/1.20          | (zip_tseitin_1 @ sk_A @ X1)
% 0.97/1.20          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.97/1.20          | ~ (v1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('sup-', [status(thm)], ['84', '89'])).
% 0.97/1.20  thf('91', plain, ((v1_relat_1 @ sk_D_2)),
% 0.97/1.20      inference('demod', [status(thm)], ['9', '10'])).
% 0.97/1.20  thf('92', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]:
% 0.97/1.20         (~ (v1_xboole_0 @ sk_A)
% 0.97/1.20          | (zip_tseitin_1 @ sk_A @ X1)
% 0.97/1.20          | (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ X0)))),
% 0.97/1.20      inference('demod', [status(thm)], ['90', '91'])).
% 0.97/1.20  thf('93', plain,
% 0.97/1.20      (![X34 : $i, X35 : $i]:
% 0.97/1.20         ((zip_tseitin_1 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.20  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.97/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.97/1.20  thf('95', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.97/1.20      inference('sup+', [status(thm)], ['93', '94'])).
% 0.97/1.20  thf('96', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]:
% 0.97/1.20         ((v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.97/1.20          | (zip_tseitin_1 @ sk_A @ X1))),
% 0.97/1.20      inference('clc', [status(thm)], ['92', '95'])).
% 0.97/1.20  thf('97', plain,
% 0.97/1.20      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('98', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.97/1.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.97/1.20  thf('99', plain,
% 0.97/1.20      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('sup-', [status(thm)], ['97', '98'])).
% 0.97/1.20  thf('100', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.97/1.20           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['1', '2'])).
% 0.97/1.20  thf('101', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.97/1.20      inference('demod', [status(thm)], ['99', '100'])).
% 0.97/1.20  thf('102', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_A @ X0)),
% 0.97/1.20      inference('sup-', [status(thm)], ['96', '101'])).
% 0.97/1.20  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.97/1.20      inference('demod', [status(thm)], ['67', '68'])).
% 0.97/1.20  thf('104', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0)),
% 0.97/1.20      inference('demod', [status(thm)], ['102', '103'])).
% 0.97/1.20  thf('105', plain, ((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)),
% 0.97/1.20      inference('demod', [status(thm)], ['76', '104'])).
% 0.97/1.20  thf('106', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.97/1.20      inference('demod', [status(thm)], ['71', '105'])).
% 0.97/1.20  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.97/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.97/1.20  thf('108', plain, ($false),
% 0.97/1.20      inference('demod', [status(thm)], ['14', '106', '107'])).
% 0.97/1.20  
% 0.97/1.20  % SZS output end Refutation
% 0.97/1.20  
% 0.97/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
