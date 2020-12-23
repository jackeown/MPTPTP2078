%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.neuqVQj4rB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:46 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 189 expanded)
%              Number of leaves         :   47 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  751 (2307 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k9_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
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

thf('5',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k9_relat_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X49: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X49 ) )
      | ~ ( r2_hidden @ X49 @ sk_C )
      | ~ ( m1_subset_1 @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('20',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_1 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_1 @ X46 @ X47 )
      | ( zip_tseitin_2 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('33',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_2 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('37',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['19','50'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['16','55','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.neuqVQj4rB
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 10:20:21 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.67/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.91  % Solved by: fo/fo7.sh
% 0.67/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.91  % done 335 iterations in 0.424s
% 0.67/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.91  % SZS output start Refutation
% 0.67/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.67/0.91  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.67/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.67/0.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.67/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.91  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.67/0.91  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.67/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.67/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.67/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.67/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.67/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.91  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.67/0.91  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.67/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.91  thf(t116_funct_2, conjecture,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ![E:$i]:
% 0.67/0.91         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.67/0.91              ( ![F:$i]:
% 0.67/0.91                ( ( m1_subset_1 @ F @ A ) =>
% 0.67/0.91                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.67/0.91                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.91            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91          ( ![E:$i]:
% 0.67/0.91            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.67/0.91                 ( ![F:$i]:
% 0.67/0.91                   ( ( m1_subset_1 @ F @ A ) =>
% 0.67/0.91                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.67/0.91                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.67/0.91    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.67/0.91  thf('0', plain,
% 0.67/0.91      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('1', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(redefinition_k7_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.67/0.91  thf('2', plain,
% 0.67/0.91      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.67/0.91          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.67/0.91  thf('3', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.67/0.91           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.91  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.67/0.91      inference('demod', [status(thm)], ['0', '3'])).
% 0.67/0.91  thf(d12_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.67/0.91       ( ![B:$i,C:$i]:
% 0.67/0.91         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.67/0.91           ( ![D:$i]:
% 0.67/0.91             ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.91               ( ?[E:$i]:
% 0.67/0.91                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.67/0.91                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.67/0.91  thf(zf_stmt_2, axiom,
% 0.67/0.91    (![E:$i,D:$i,B:$i,A:$i]:
% 0.67/0.91     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.67/0.91       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.67/0.91         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_3, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.91       ( ![B:$i,C:$i]:
% 0.67/0.91         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.67/0.91           ( ![D:$i]:
% 0.67/0.91             ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.91               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.67/0.91  thf('5', plain,
% 0.67/0.91      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 0.67/0.91         (((X22) != (k9_relat_1 @ X20 @ X19))
% 0.67/0.91          | (zip_tseitin_0 @ (sk_E_1 @ X23 @ X19 @ X20) @ X23 @ X19 @ X20)
% 0.67/0.91          | ~ (r2_hidden @ X23 @ X22)
% 0.67/0.91          | ~ (v1_funct_1 @ X20)
% 0.67/0.91          | ~ (v1_relat_1 @ X20))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.91  thf('6', plain,
% 0.67/0.91      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X20)
% 0.67/0.91          | ~ (v1_funct_1 @ X20)
% 0.67/0.91          | ~ (r2_hidden @ X23 @ (k9_relat_1 @ X20 @ X19))
% 0.67/0.91          | (zip_tseitin_0 @ (sk_E_1 @ X23 @ X19 @ X20) @ X23 @ X19 @ X20))),
% 0.67/0.91      inference('simplify', [status(thm)], ['5'])).
% 0.67/0.91  thf('7', plain,
% 0.67/0.91      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.67/0.91         sk_D_2)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_D_2)
% 0.67/0.91        | ~ (v1_relat_1 @ sk_D_2))),
% 0.67/0.91      inference('sup-', [status(thm)], ['4', '6'])).
% 0.67/0.91  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('9', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(cc1_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( v1_relat_1 @ C ) ))).
% 0.67/0.91  thf('10', plain,
% 0.67/0.91      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.67/0.91         ((v1_relat_1 @ X28)
% 0.67/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.91  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.67/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.91  thf('12', plain,
% 0.67/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.67/0.91        sk_D_2)),
% 0.67/0.91      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.67/0.91  thf('13', plain,
% 0.67/0.91      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.91         ((r2_hidden @ X14 @ X16) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.91  thf('14', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.67/0.91  thf('15', plain,
% 0.67/0.91      (![X49 : $i]:
% 0.67/0.91         (((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X49))
% 0.67/0.91          | ~ (r2_hidden @ X49 @ sk_C)
% 0.67/0.91          | ~ (m1_subset_1 @ X49 @ sk_A))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('16', plain,
% 0.67/0.91      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.67/0.91        | ((sk_E_2)
% 0.67/0.91            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.91  thf('17', plain,
% 0.67/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.67/0.91        sk_D_2)),
% 0.67/0.91      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.67/0.91  thf('18', plain,
% 0.67/0.91      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.91         ((r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.67/0.91          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.91  thf('19', plain,
% 0.67/0.91      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.67/0.91      inference('sup-', [status(thm)], ['17', '18'])).
% 0.67/0.91  thf(d1_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.67/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.67/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.67/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_4, axiom,
% 0.67/0.91    (![B:$i,A:$i]:
% 0.67/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.91       ( zip_tseitin_1 @ B @ A ) ))).
% 0.67/0.91  thf('20', plain,
% 0.67/0.91      (![X41 : $i, X42 : $i]:
% 0.67/0.91         ((zip_tseitin_1 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.67/0.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.91  thf('21', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.67/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.91  thf('22', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.67/0.91      inference('sup+', [status(thm)], ['20', '21'])).
% 0.67/0.91  thf(d1_xboole_0, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.91  thf('23', plain,
% 0.67/0.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.67/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.91  thf(t7_ordinal1, axiom,
% 0.67/0.91    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.91  thf('24', plain,
% 0.67/0.91      (![X26 : $i, X27 : $i]:
% 0.67/0.91         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.67/0.91      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.67/0.91  thf('25', plain,
% 0.67/0.91      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['23', '24'])).
% 0.67/0.91  thf('26', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]: ((zip_tseitin_1 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['22', '25'])).
% 0.67/0.91  thf('27', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(cc4_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( v1_xboole_0 @ A ) =>
% 0.67/0.91       ( ![C:$i]:
% 0.67/0.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.67/0.91           ( v1_xboole_0 @ C ) ) ) ))).
% 0.67/0.91  thf('28', plain,
% 0.67/0.91      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.67/0.91         (~ (v1_xboole_0 @ X31)
% 0.67/0.91          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.67/0.91          | (v1_xboole_0 @ X32))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.67/0.91  thf('29', plain, (((v1_xboole_0 @ sk_D_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.67/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.67/0.91  thf('30', plain,
% 0.67/0.91      (![X0 : $i]: ((zip_tseitin_1 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D_2))),
% 0.67/0.91      inference('sup-', [status(thm)], ['26', '29'])).
% 0.67/0.91  thf('31', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.67/0.91  thf(zf_stmt_6, axiom,
% 0.67/0.91    (![C:$i,B:$i,A:$i]:
% 0.67/0.91     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.67/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 0.67/0.91  thf(zf_stmt_8, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.67/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.67/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.67/0.91  thf('32', plain,
% 0.67/0.91      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.67/0.91         (~ (zip_tseitin_1 @ X46 @ X47)
% 0.67/0.91          | (zip_tseitin_2 @ X48 @ X46 @ X47)
% 0.67/0.91          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.67/0.91  thf('33', plain,
% 0.67/0.91      (((zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.67/0.91        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['31', '32'])).
% 0.67/0.91  thf('34', plain,
% 0.67/0.91      (((v1_xboole_0 @ sk_D_2) | (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['30', '33'])).
% 0.67/0.91  thf('35', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('36', plain,
% 0.67/0.91      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.67/0.91         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.67/0.91          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.67/0.91          | ~ (zip_tseitin_2 @ X45 @ X44 @ X43))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.67/0.91  thf('37', plain,
% 0.67/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.67/0.91        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('38', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(redefinition_k1_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.67/0.91  thf('39', plain,
% 0.67/0.91      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.67/0.91         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.67/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.67/0.91  thf('40', plain,
% 0.67/0.91      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.67/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.67/0.91  thf('41', plain,
% 0.67/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.67/0.91        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.67/0.91      inference('demod', [status(thm)], ['37', '40'])).
% 0.67/0.91  thf('42', plain,
% 0.67/0.91      (((v1_xboole_0 @ sk_D_2) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['34', '41'])).
% 0.67/0.91  thf('43', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.67/0.91      inference('demod', [status(thm)], ['0', '3'])).
% 0.67/0.91  thf(t143_relat_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( v1_relat_1 @ C ) =>
% 0.67/0.91       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.67/0.91         ( ?[D:$i]:
% 0.67/0.91           ( ( r2_hidden @ D @ B ) & 
% 0.67/0.91             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.67/0.91             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.67/0.91  thf('44', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.91         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.67/0.91          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.67/0.91          | ~ (v1_relat_1 @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.67/0.91  thf('45', plain,
% 0.67/0.91      ((~ (v1_relat_1 @ sk_D_2)
% 0.67/0.91        | (r2_hidden @ 
% 0.67/0.91           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.67/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.91  thf('46', plain, ((v1_relat_1 @ sk_D_2)),
% 0.67/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.91  thf('47', plain,
% 0.67/0.91      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.67/0.91        sk_D_2)),
% 0.67/0.91      inference('demod', [status(thm)], ['45', '46'])).
% 0.67/0.91  thf('48', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.91  thf('49', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.67/0.91      inference('sup-', [status(thm)], ['47', '48'])).
% 0.67/0.91  thf('50', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.67/0.91      inference('sup-', [status(thm)], ['42', '49'])).
% 0.67/0.91  thf('51', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['19', '50'])).
% 0.67/0.91  thf(d2_subset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( ( v1_xboole_0 @ A ) =>
% 0.67/0.91         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.67/0.91       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.91         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.91  thf('52', plain,
% 0.67/0.91      (![X4 : $i, X5 : $i]:
% 0.67/0.91         (~ (r2_hidden @ X4 @ X5)
% 0.67/0.91          | (m1_subset_1 @ X4 @ X5)
% 0.67/0.91          | (v1_xboole_0 @ X5))),
% 0.67/0.91      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.91  thf('53', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.91  thf('54', plain,
% 0.67/0.91      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.67/0.91      inference('clc', [status(thm)], ['52', '53'])).
% 0.67/0.91  thf('55', plain, ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['51', '54'])).
% 0.67/0.91  thf('56', plain,
% 0.67/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.67/0.91        sk_D_2)),
% 0.67/0.91      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.67/0.91  thf('57', plain,
% 0.67/0.91      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.91         (((X15) = (k1_funct_1 @ X13 @ X14))
% 0.67/0.91          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.91  thf('58', plain,
% 0.67/0.91      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['56', '57'])).
% 0.67/0.91  thf('59', plain, (((sk_E_2) != (sk_E_2))),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '55', '58'])).
% 0.67/0.91  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.67/0.91  
% 0.67/0.91  % SZS output end Refutation
% 0.67/0.91  
% 0.67/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
