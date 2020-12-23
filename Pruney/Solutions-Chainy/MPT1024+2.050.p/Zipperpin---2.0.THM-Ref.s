%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X8Eari0DXY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:41 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  142 (1518 expanded)
%              Number of leaves         :   43 ( 461 expanded)
%              Depth                    :   21
%              Number of atoms          :  978 (21742 expanded)
%              Number of equality atoms :   66 ( 929 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_2 @ X35 @ X34 @ X33 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_1 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_1 @ X36 @ X37 )
      | ( zip_tseitin_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_A )
      | ~ ( r2_hidden @ X39 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('43',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('46',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['21','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 != k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('66',plain,(
    ~ ( r1_tarski @ sk_D_2 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_1 @ X36 @ X37 )
      | ( zip_tseitin_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_1 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_1 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    ! [X31: $i] :
      ( zip_tseitin_1 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
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
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_1 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('89',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_A @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_A @ X0 ) ),
    inference(condensation,[status(thm)],['90'])).

thf('92',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('93',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['76','93'])).

thf('95',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['71','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['14','95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X8Eari0DXY
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:18:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 221 iterations in 0.352s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.82  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.58/0.82  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.58/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.58/0.82  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.82  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.58/0.82  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.58/0.82  thf(t115_funct_2, conjecture,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82       ( ![E:$i]:
% 0.58/0.82         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.58/0.82              ( ![F:$i]:
% 0.58/0.82                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.58/0.82                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.82            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82          ( ![E:$i]:
% 0.58/0.82            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.58/0.82                 ( ![F:$i]:
% 0.58/0.82                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.58/0.82                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.58/0.82          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.58/0.82           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.82  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.82  thf(t143_relat_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( v1_relat_1 @ C ) =>
% 0.58/0.82       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.58/0.82         ( ?[D:$i]:
% 0.58/0.82           ( ( r2_hidden @ D @ B ) & 
% 0.58/0.82             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.58/0.82             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.58/0.82          | (r2_hidden @ (sk_D @ X8 @ X6 @ X7) @ (k1_relat_1 @ X8))
% 0.58/0.82          | ~ (v1_relat_1 @ X8))),
% 0.58/0.82      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      ((~ (v1_relat_1 @ sk_D_2)
% 0.58/0.82        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc2_relat_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( v1_relat_1 @ A ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.82  thf('8', plain,
% 0.58/0.82      (![X1 : $i, X2 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.58/0.82          | (v1_relat_1 @ X1)
% 0.58/0.82          | ~ (v1_relat_1 @ X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.82  thf(fc6_relat_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.58/0.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.82  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2))),
% 0.58/0.82      inference('demod', [status(thm)], ['6', '11'])).
% 0.58/0.82  thf(t7_ordinal1, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.82  thf('13', plain,
% 0.58/0.82      (![X22 : $i, X23 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.58/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.82  thf('14', plain,
% 0.58/0.82      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.82  thf('15', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(d1_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_1, axiom,
% 0.58/0.82    (![C:$i,B:$i,A:$i]:
% 0.58/0.82     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.58/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.82         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.58/0.82          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.58/0.82          | ~ (zip_tseitin_2 @ X35 @ X34 @ X33))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf('17', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.82         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.58/0.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.82  thf('21', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['17', '20'])).
% 0.58/0.82  thf(zf_stmt_2, axiom,
% 0.58/0.82    (![B:$i,A:$i]:
% 0.58/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82       ( zip_tseitin_1 @ B @ A ) ))).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      (![X31 : $i, X32 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.82  thf('23', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_5, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.58/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.58/0.82         (~ (zip_tseitin_1 @ X36 @ X37)
% 0.58/0.82          | (zip_tseitin_2 @ X38 @ X36 @ X37)
% 0.58/0.82          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.82  thf('25', plain,
% 0.58/0.82      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.82        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['22', '25'])).
% 0.58/0.82  thf('27', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['17', '20'])).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.82  thf('29', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.82  thf(d12_funct_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i,C:$i]:
% 0.58/0.82         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.58/0.82           ( ![D:$i]:
% 0.58/0.82             ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.82               ( ?[E:$i]:
% 0.58/0.82                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.58/0.82                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_7, axiom,
% 0.58/0.82    (![E:$i,D:$i,B:$i,A:$i]:
% 0.58/0.82     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.58/0.82       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.58/0.82         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_8, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i,C:$i]:
% 0.58/0.82         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.58/0.82           ( ![D:$i]:
% 0.58/0.82             ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.82               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.58/0.82         (((X18) != (k9_relat_1 @ X16 @ X15))
% 0.58/0.82          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16)
% 0.58/0.82          | ~ (r2_hidden @ X19 @ X18)
% 0.58/0.82          | ~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (v1_relat_1 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ X16)
% 0.58/0.82          | ~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (r2_hidden @ X19 @ (k9_relat_1 @ X16 @ X15))
% 0.58/0.82          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16))),
% 0.58/0.82      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.82  thf('32', plain,
% 0.58/0.82      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.58/0.82         sk_D_2)
% 0.58/0.82        | ~ (v1_funct_1 @ sk_D_2)
% 0.58/0.82        | ~ (v1_relat_1 @ sk_D_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['29', '31'])).
% 0.58/0.82  thf('33', plain, ((v1_funct_1 @ sk_D_2)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.58/0.82        sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         ((r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.58/0.82          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.58/0.82  thf('37', plain,
% 0.58/0.82      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.82  thf('38', plain,
% 0.58/0.82      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.58/0.82        | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['28', '37'])).
% 0.58/0.82  thf('39', plain,
% 0.58/0.82      (![X39 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X39 @ sk_A)
% 0.58/0.82          | ~ (r2_hidden @ X39 @ sk_C)
% 0.58/0.82          | ((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X39)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      ((((sk_B) = (k1_xboole_0))
% 0.58/0.82        | ((sk_E_2)
% 0.58/0.82            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))
% 0.58/0.82        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C))),
% 0.58/0.82      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.58/0.82        sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         (((X11) = (k1_funct_1 @ X9 @ X10))
% 0.58/0.82          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.58/0.82        sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.58/0.82  thf('45', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         ((r2_hidden @ X10 @ X12) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.58/0.82  thf('46', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.58/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.82  thf('47', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_2) != (sk_E_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['40', '43', '46'])).
% 0.58/0.82  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['21', '48'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.58/0.82  thf('52', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ 
% 0.58/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['50', '51'])).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.58/0.82         (((X36) != (k1_xboole_0))
% 0.58/0.82          | ((X37) = (k1_xboole_0))
% 0.58/0.82          | ((X38) = (k1_xboole_0))
% 0.58/0.82          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.58/0.82          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.82  thf('54', plain,
% 0.58/0.82      (![X37 : $i, X38 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X38 @ 
% 0.58/0.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ k1_xboole_0)))
% 0.58/0.82          | ~ (v1_funct_2 @ X38 @ X37 @ k1_xboole_0)
% 0.58/0.82          | ((X38) = (k1_xboole_0))
% 0.58/0.82          | ((X37) = (k1_xboole_0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['53'])).
% 0.58/0.82  thf('55', plain,
% 0.58/0.82      ((((sk_A) = (k1_xboole_0))
% 0.58/0.82        | ((sk_D_2) = (k1_xboole_0))
% 0.58/0.82        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['52', '54'])).
% 0.58/0.82  thf('56', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.58/0.82  thf('58', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['56', '57'])).
% 0.58/0.82  thf('59', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['55', '58'])).
% 0.58/0.82  thf('60', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ (sk_D @ X8 @ X6 @ X7) @ X7) @ X8)
% 0.58/0.82          | ~ (v1_relat_1 @ X8))),
% 0.58/0.82      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.82  thf('62', plain,
% 0.58/0.82      ((~ (v1_relat_1 @ sk_D_2)
% 0.58/0.82        | (r2_hidden @ 
% 0.58/0.82           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.82  thf('63', plain, ((v1_relat_1 @ sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf('64', plain,
% 0.58/0.82      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.58/0.82        sk_D_2)),
% 0.58/0.82      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.82  thf('65', plain,
% 0.58/0.82      (![X22 : $i, X23 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.58/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.82  thf('66', plain,
% 0.58/0.82      (~ (r1_tarski @ sk_D_2 @ 
% 0.58/0.82          (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.58/0.82           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2))
% 0.58/0.82        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['59', '66'])).
% 0.58/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.82  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.82  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['67', '68'])).
% 0.58/0.82  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['67', '68'])).
% 0.58/0.82  thf('71', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.58/0.82        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['49', '69', '70'])).
% 0.58/0.82  thf('72', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ 
% 0.58/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['50', '51'])).
% 0.58/0.82  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['67', '68'])).
% 0.58/0.82  thf('74', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_2 @ 
% 0.58/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['72', '73'])).
% 0.58/0.82  thf('75', plain,
% 0.58/0.82      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.58/0.82         (~ (zip_tseitin_1 @ X36 @ X37)
% 0.58/0.82          | (zip_tseitin_2 @ X38 @ X36 @ X37)
% 0.58/0.82          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.82  thf('76', plain,
% 0.58/0.82      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.58/0.82        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.82  thf('77', plain,
% 0.58/0.82      (![X31 : $i, X32 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.82  thf('78', plain,
% 0.58/0.82      (![X31 : $i, X32 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.82  thf('79', plain, (![X31 : $i]: (zip_tseitin_1 @ X31 @ k1_xboole_0)),
% 0.58/0.82      inference('simplify', [status(thm)], ['78'])).
% 0.58/0.82  thf('80', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.58/0.82      inference('sup+', [status(thm)], ['77', '79'])).
% 0.58/0.82  thf('81', plain,
% 0.58/0.82      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.82        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.82  thf('82', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ sk_A @ X0) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['80', '81'])).
% 0.58/0.82  thf('83', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['17', '20'])).
% 0.58/0.82  thf('84', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['82', '83'])).
% 0.58/0.82  thf('85', plain,
% 0.58/0.82      (![X31 : $i, X32 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.82  thf('86', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.82  thf('87', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.58/0.82      inference('sup+', [status(thm)], ['85', '86'])).
% 0.58/0.82  thf('88', plain,
% 0.58/0.82      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.82  thf('89', plain, (![X0 : $i]: (zip_tseitin_1 @ (k1_relat_1 @ sk_D_2) @ X0)),
% 0.58/0.82      inference('sup-', [status(thm)], ['87', '88'])).
% 0.58/0.82  thf('90', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ sk_A @ X0) | (zip_tseitin_1 @ sk_A @ X1))),
% 0.58/0.82      inference('sup+', [status(thm)], ['84', '89'])).
% 0.58/0.82  thf('91', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_A @ X0)),
% 0.58/0.82      inference('condensation', [status(thm)], ['90'])).
% 0.58/0.82  thf('92', plain, (((sk_A) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['67', '68'])).
% 0.58/0.82  thf('93', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('demod', [status(thm)], ['91', '92'])).
% 0.58/0.82  thf('94', plain, ((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['76', '93'])).
% 0.58/0.82  thf('95', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.58/0.82      inference('demod', [status(thm)], ['71', '94'])).
% 0.58/0.82  thf('96', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.82  thf('97', plain, ($false),
% 0.58/0.82      inference('demod', [status(thm)], ['14', '95', '96'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
