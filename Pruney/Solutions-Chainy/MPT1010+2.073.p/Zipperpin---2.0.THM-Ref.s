%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dymZFE0zPO

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:23 EST 2020

% Result     : Theorem 36.26s
% Output     : Refutation 36.26s
% Verified   : 
% Statistics : Number of formulae       :  167 (1180 expanded)
%              Number of leaves         :   43 ( 361 expanded)
%              Depth                    :   23
%              Number of atoms          : 1328 (14960 expanded)
%              Number of equality atoms :  134 (1008 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('6',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) )
    | ( sk_D_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X26 ) @ X24 )
      | ( X26
       != ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_D_2 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('47',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('48',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('50',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_B @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_D_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('63',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('68',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_tarski @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['38','67','68'])).

thf('70',plain,
    ( ( sk_D_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k2_tarski @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('77',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('81',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ( X25
       != ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('82',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_funct_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( zip_tseitin_0 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_D_2 @ X0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('97',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('98',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) )
    | ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('100',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( sk_A
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','101'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

thf('105',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('108',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('109',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

thf('116',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('117',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['114','117'])).

thf('119',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','118'])).

thf('120',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['2','120','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dymZFE0zPO
% 0.13/0.39  % Computer   : n024.cluster.edu
% 0.13/0.39  % Model      : x86_64 x86_64
% 0.13/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.39  % Memory     : 8042.1875MB
% 0.13/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.39  % CPULimit   : 60
% 0.13/0.39  % DateTime   : Tue Dec  1 17:03:06 EST 2020
% 0.13/0.39  % CPUTime    : 
% 0.13/0.39  % Running portfolio for 600 s
% 0.13/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.39  % Number of cores: 8
% 0.13/0.39  % Python version: Python 3.6.8
% 0.13/0.39  % Running in FO mode
% 36.26/36.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.26/36.48  % Solved by: fo/fo7.sh
% 36.26/36.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.26/36.48  % done 7982 iterations in 35.977s
% 36.26/36.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.26/36.48  % SZS output start Refutation
% 36.26/36.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 36.26/36.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.26/36.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 36.26/36.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 36.26/36.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 36.26/36.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 36.26/36.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 36.26/36.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.26/36.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 36.26/36.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 36.26/36.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 36.26/36.48  thf(sk_A_type, type, sk_A: $i).
% 36.26/36.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 36.26/36.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 36.26/36.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 36.26/36.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 36.26/36.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 36.26/36.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 36.26/36.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.26/36.48  thf(sk_D_2_type, type, sk_D_2: $i).
% 36.26/36.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.26/36.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 36.26/36.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 36.26/36.48  thf(sk_B_type, type, sk_B: $i > $i).
% 36.26/36.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 36.26/36.48  thf(t65_funct_2, conjecture,
% 36.26/36.48    (![A:$i,B:$i,C:$i,D:$i]:
% 36.26/36.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 36.26/36.48         ( m1_subset_1 @
% 36.26/36.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 36.26/36.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 36.26/36.48  thf(zf_stmt_0, negated_conjecture,
% 36.26/36.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 36.26/36.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 36.26/36.48            ( m1_subset_1 @
% 36.26/36.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 36.26/36.48          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 36.26/36.48    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 36.26/36.48  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf(t7_ordinal1, axiom,
% 36.26/36.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.26/36.48  thf('1', plain,
% 36.26/36.48      (![X27 : $i, X28 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 36.26/36.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.26/36.48  thf('2', plain, (~ (r1_tarski @ sk_A @ sk_C_1)),
% 36.26/36.48      inference('sup-', [status(thm)], ['0', '1'])).
% 36.26/36.48  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf(d1_funct_2, axiom,
% 36.26/36.48    (![A:$i,B:$i,C:$i]:
% 36.26/36.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.26/36.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 36.26/36.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 36.26/36.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 36.26/36.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 36.26/36.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 36.26/36.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 36.26/36.48  thf(zf_stmt_1, axiom,
% 36.26/36.48    (![B:$i,A:$i]:
% 36.26/36.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 36.26/36.48       ( zip_tseitin_0 @ B @ A ) ))).
% 36.26/36.48  thf('4', plain,
% 36.26/36.48      (![X41 : $i, X42 : $i]:
% 36.26/36.48         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.26/36.48  thf('5', plain,
% 36.26/36.48      ((m1_subset_1 @ sk_D_2 @ 
% 36.26/36.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 36.26/36.48  thf(zf_stmt_3, axiom,
% 36.26/36.48    (![C:$i,B:$i,A:$i]:
% 36.26/36.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 36.26/36.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 36.26/36.48  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 36.26/36.48  thf(zf_stmt_5, axiom,
% 36.26/36.48    (![A:$i,B:$i,C:$i]:
% 36.26/36.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.26/36.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 36.26/36.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 36.26/36.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 36.26/36.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 36.26/36.48  thf('6', plain,
% 36.26/36.48      (![X46 : $i, X47 : $i, X48 : $i]:
% 36.26/36.48         (~ (zip_tseitin_0 @ X46 @ X47)
% 36.26/36.48          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 36.26/36.48          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.26/36.48  thf('7', plain,
% 36.26/36.48      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 36.26/36.48      inference('sup-', [status(thm)], ['5', '6'])).
% 36.26/36.48  thf('8', plain,
% 36.26/36.48      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 36.26/36.48        | (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 36.26/36.48      inference('sup-', [status(thm)], ['4', '7'])).
% 36.26/36.48  thf('9', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('10', plain,
% 36.26/36.48      (![X43 : $i, X44 : $i, X45 : $i]:
% 36.26/36.48         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 36.26/36.48          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 36.26/36.48          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 36.26/36.48  thf('11', plain,
% 36.26/36.48      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['9', '10'])).
% 36.26/36.48  thf('12', plain,
% 36.26/36.48      ((m1_subset_1 @ sk_D_2 @ 
% 36.26/36.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf(redefinition_k1_relset_1, axiom,
% 36.26/36.48    (![A:$i,B:$i,C:$i]:
% 36.26/36.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.26/36.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 36.26/36.48  thf('13', plain,
% 36.26/36.48      (![X32 : $i, X33 : $i, X34 : $i]:
% 36.26/36.48         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 36.26/36.48          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 36.26/36.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 36.26/36.48  thf('14', plain,
% 36.26/36.48      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 36.26/36.48         = (k1_relat_1 @ sk_D_2))),
% 36.26/36.48      inference('sup-', [status(thm)], ['12', '13'])).
% 36.26/36.48  thf('15', plain,
% 36.26/36.48      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('demod', [status(thm)], ['11', '14'])).
% 36.26/36.48  thf('16', plain,
% 36.26/36.48      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['8', '15'])).
% 36.26/36.48  thf('17', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('18', plain,
% 36.26/36.48      (((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['16', '17'])).
% 36.26/36.48  thf('19', plain,
% 36.26/36.48      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['8', '15'])).
% 36.26/36.48  thf('20', plain,
% 36.26/36.48      ((m1_subset_1 @ sk_D_2 @ 
% 36.26/36.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('21', plain,
% 36.26/36.48      (((m1_subset_1 @ sk_D_2 @ 
% 36.26/36.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['19', '20'])).
% 36.26/36.48  thf('22', plain,
% 36.26/36.48      (![X46 : $i, X47 : $i, X48 : $i]:
% 36.26/36.48         (((X46) != (k1_xboole_0))
% 36.26/36.48          | ((X47) = (k1_xboole_0))
% 36.26/36.48          | ((X48) = (k1_xboole_0))
% 36.26/36.48          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 36.26/36.48          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 36.26/36.48  thf('23', plain,
% 36.26/36.48      (![X47 : $i, X48 : $i]:
% 36.26/36.48         (~ (m1_subset_1 @ X48 @ 
% 36.26/36.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ k1_xboole_0)))
% 36.26/36.48          | ~ (v1_funct_2 @ X48 @ X47 @ k1_xboole_0)
% 36.26/36.48          | ((X48) = (k1_xboole_0))
% 36.26/36.48          | ((X47) = (k1_xboole_0)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['22'])).
% 36.26/36.48  thf('24', plain,
% 36.26/36.48      ((((sk_A) = (k1_relat_1 @ sk_D_2))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_D_2) = (k1_xboole_0))
% 36.26/36.48        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 36.26/36.48      inference('sup-', [status(thm)], ['21', '23'])).
% 36.26/36.48  thf('25', plain,
% 36.26/36.48      ((((sk_A) = (k1_relat_1 @ sk_D_2))
% 36.26/36.48        | ((sk_D_2) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['18', '24'])).
% 36.26/36.48  thf('26', plain,
% 36.26/36.48      ((((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_D_2) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['25'])).
% 36.26/36.48  thf(d4_funct_1, axiom,
% 36.26/36.48    (![A:$i]:
% 36.26/36.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 36.26/36.48       ( ![B:$i,C:$i]:
% 36.26/36.48         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 36.26/36.48             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 36.26/36.48               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 36.26/36.48           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 36.26/36.48             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 36.26/36.48               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 36.26/36.48  thf('27', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i, X26 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X23 @ X26) @ X24)
% 36.26/36.48          | ((X26) != (k1_funct_1 @ X24 @ X23))
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | ~ (v1_relat_1 @ X24))),
% 36.26/36.48      inference('cnf', [status(esa)], [d4_funct_1])).
% 36.26/36.48  thf('28', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i]:
% 36.26/36.48         (~ (v1_relat_1 @ X24)
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 36.26/36.48          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['27'])).
% 36.26/36.48  thf('29', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X0 @ sk_A)
% 36.26/36.48          | ((sk_D_2) = (k1_xboole_0))
% 36.26/36.48          | ((sk_A) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2)
% 36.26/36.48          | ~ (v1_funct_1 @ sk_D_2)
% 36.26/36.48          | ~ (v1_relat_1 @ sk_D_2))),
% 36.26/36.48      inference('sup-', [status(thm)], ['26', '28'])).
% 36.26/36.48  thf('30', plain, ((v1_funct_1 @ sk_D_2)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('31', plain,
% 36.26/36.48      ((m1_subset_1 @ sk_D_2 @ 
% 36.26/36.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf(cc1_relset_1, axiom,
% 36.26/36.48    (![A:$i,B:$i,C:$i]:
% 36.26/36.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 36.26/36.48       ( v1_relat_1 @ C ) ))).
% 36.26/36.48  thf('32', plain,
% 36.26/36.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 36.26/36.48         ((v1_relat_1 @ X29)
% 36.26/36.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 36.26/36.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 36.26/36.48  thf('33', plain, ((v1_relat_1 @ sk_D_2)),
% 36.26/36.48      inference('sup-', [status(thm)], ['31', '32'])).
% 36.26/36.48  thf('34', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X0 @ sk_A)
% 36.26/36.48          | ((sk_D_2) = (k1_xboole_0))
% 36.26/36.48          | ((sk_A) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2))),
% 36.26/36.48      inference('demod', [status(thm)], ['29', '30', '33'])).
% 36.26/36.48  thf('35', plain,
% 36.26/36.48      (((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1)) @ 
% 36.26/36.48         sk_D_2)
% 36.26/36.48        | ((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_D_2) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['3', '34'])).
% 36.26/36.48  thf('36', plain,
% 36.26/36.48      ((m1_subset_1 @ sk_D_2 @ 
% 36.26/36.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf(l3_subset_1, axiom,
% 36.26/36.48    (![A:$i,B:$i]:
% 36.26/36.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 36.26/36.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 36.26/36.48  thf('37', plain,
% 36.26/36.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X20 @ X21)
% 36.26/36.48          | (r2_hidden @ X20 @ X22)
% 36.26/36.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 36.26/36.48      inference('cnf', [status(esa)], [l3_subset_1])).
% 36.26/36.48  thf('38', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 36.26/36.48          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 36.26/36.48      inference('sup-', [status(thm)], ['36', '37'])).
% 36.26/36.48  thf('39', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('40', plain,
% 36.26/36.48      (![X41 : $i, X42 : $i]:
% 36.26/36.48         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.26/36.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 36.26/36.48  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.26/36.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.26/36.48  thf('42', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.26/36.48         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 36.26/36.48      inference('sup+', [status(thm)], ['40', '41'])).
% 36.26/36.48  thf('43', plain,
% 36.26/36.48      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 36.26/36.48      inference('sup-', [status(thm)], ['5', '6'])).
% 36.26/36.48  thf('44', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         ((r1_tarski @ (k1_tarski @ sk_B_1) @ X0)
% 36.26/36.48          | (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 36.26/36.48      inference('sup-', [status(thm)], ['42', '43'])).
% 36.26/36.48  thf('45', plain,
% 36.26/36.48      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('demod', [status(thm)], ['11', '14'])).
% 36.26/36.48  thf('46', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         ((r1_tarski @ (k1_tarski @ sk_B_1) @ X0)
% 36.26/36.48          | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['44', '45'])).
% 36.26/36.48  thf(t6_mcart_1, axiom,
% 36.26/36.48    (![A:$i]:
% 36.26/36.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 36.26/36.48          ( ![B:$i]:
% 36.26/36.48            ( ~( ( r2_hidden @ B @ A ) & 
% 36.26/36.48                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 36.26/36.48                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 36.26/36.48                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 36.26/36.48                       ( r2_hidden @ G @ B ) ) =>
% 36.26/36.48                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 36.26/36.48  thf('47', plain,
% 36.26/36.48      (![X35 : $i]:
% 36.26/36.48         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X35) @ X35))),
% 36.26/36.48      inference('cnf', [status(esa)], [t6_mcart_1])).
% 36.26/36.48  thf(t31_zfmisc_1, axiom,
% 36.26/36.48    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 36.26/36.48  thf('48', plain, (![X19 : $i]: ((k3_tarski @ (k1_tarski @ X19)) = (X19))),
% 36.26/36.48      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 36.26/36.48  thf(d4_tarski, axiom,
% 36.26/36.48    (![A:$i,B:$i]:
% 36.26/36.48     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 36.26/36.48       ( ![C:$i]:
% 36.26/36.48         ( ( r2_hidden @ C @ B ) <=>
% 36.26/36.48           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 36.26/36.48  thf('49', plain,
% 36.26/36.48      (![X8 : $i, X10 : $i, X11 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X11 @ X10)
% 36.26/36.48          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 36.26/36.48          | ((X10) != (k3_tarski @ X8)))),
% 36.26/36.48      inference('cnf', [status(esa)], [d4_tarski])).
% 36.26/36.48  thf('50', plain,
% 36.26/36.48      (![X8 : $i, X11 : $i]:
% 36.26/36.48         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 36.26/36.48          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['49'])).
% 36.26/36.48  thf('51', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X1 @ X0)
% 36.26/36.48          | (r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['48', '50'])).
% 36.26/36.48  thf('52', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (((X0) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ (sk_D_1 @ (sk_B @ X0) @ (k1_tarski @ X0)) @ 
% 36.26/36.48             (k1_tarski @ X0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['47', '51'])).
% 36.26/36.48  thf('53', plain,
% 36.26/36.48      (![X27 : $i, X28 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 36.26/36.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.26/36.48  thf('54', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (((X0) = (k1_xboole_0))
% 36.26/36.48          | ~ (r1_tarski @ (k1_tarski @ X0) @ 
% 36.26/36.48               (sk_D_1 @ (sk_B @ X0) @ (k1_tarski @ X0))))),
% 36.26/36.48      inference('sup-', [status(thm)], ['52', '53'])).
% 36.26/36.48  thf('55', plain,
% 36.26/36.48      ((((sk_A) = (k1_relat_1 @ sk_D_2)) | ((sk_B_1) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['46', '54'])).
% 36.26/36.48  thf('56', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i]:
% 36.26/36.48         (~ (v1_relat_1 @ X24)
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 36.26/36.48          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['27'])).
% 36.26/36.48  thf('57', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X0 @ sk_A)
% 36.26/36.48          | ((sk_B_1) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2)
% 36.26/36.48          | ~ (v1_funct_1 @ sk_D_2)
% 36.26/36.48          | ~ (v1_relat_1 @ sk_D_2))),
% 36.26/36.48      inference('sup-', [status(thm)], ['55', '56'])).
% 36.26/36.48  thf('58', plain, ((v1_funct_1 @ sk_D_2)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('59', plain, ((v1_relat_1 @ sk_D_2)),
% 36.26/36.48      inference('sup-', [status(thm)], ['31', '32'])).
% 36.26/36.48  thf('60', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X0 @ sk_A)
% 36.26/36.48          | ((sk_B_1) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2))),
% 36.26/36.48      inference('demod', [status(thm)], ['57', '58', '59'])).
% 36.26/36.48  thf('61', plain,
% 36.26/36.48      (((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1)) @ 
% 36.26/36.48         sk_D_2)
% 36.26/36.48        | ((sk_B_1) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['39', '60'])).
% 36.26/36.48  thf('62', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 36.26/36.48          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 36.26/36.48      inference('sup-', [status(thm)], ['36', '37'])).
% 36.26/36.48  thf('63', plain,
% 36.26/36.48      ((((sk_B_1) = (k1_xboole_0))
% 36.26/36.48        | (r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1)) @ 
% 36.26/36.48           (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 36.26/36.48      inference('sup-', [status(thm)], ['61', '62'])).
% 36.26/36.48  thf(t129_zfmisc_1, axiom,
% 36.26/36.48    (![A:$i,B:$i,C:$i,D:$i]:
% 36.26/36.48     ( ( r2_hidden @
% 36.26/36.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 36.26/36.48       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 36.26/36.48  thf('64', plain,
% 36.26/36.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 36.26/36.48         (((X16) = (X17))
% 36.26/36.48          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ 
% 36.26/36.48               (k2_zfmisc_1 @ X15 @ (k1_tarski @ X17))))),
% 36.26/36.48      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 36.26/36.48  thf('65', plain,
% 36.26/36.48      ((((sk_B_1) = (k1_xboole_0))
% 36.26/36.48        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['63', '64'])).
% 36.26/36.48  thf('66', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('67', plain, (((sk_B_1) = (k1_xboole_0))),
% 36.26/36.48      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 36.26/36.48  thf(t69_enumset1, axiom,
% 36.26/36.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 36.26/36.48  thf('68', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 36.26/36.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 36.26/36.48  thf('69', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         ((r2_hidden @ X0 @ 
% 36.26/36.48           (k2_zfmisc_1 @ sk_A @ (k2_tarski @ k1_xboole_0 @ k1_xboole_0)))
% 36.26/36.48          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 36.26/36.48      inference('demod', [status(thm)], ['38', '67', '68'])).
% 36.26/36.48  thf('70', plain,
% 36.26/36.48      ((((sk_D_2) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0))
% 36.26/36.48        | (r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1)) @ 
% 36.26/36.48           (k2_zfmisc_1 @ sk_A @ (k2_tarski @ k1_xboole_0 @ k1_xboole_0))))),
% 36.26/36.48      inference('sup-', [status(thm)], ['35', '69'])).
% 36.26/36.48  thf('71', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 36.26/36.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 36.26/36.48  thf('72', plain,
% 36.26/36.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 36.26/36.48         (((X16) = (X17))
% 36.26/36.48          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ 
% 36.26/36.48               (k2_zfmisc_1 @ X15 @ (k1_tarski @ X17))))),
% 36.26/36.48      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 36.26/36.48  thf('73', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.26/36.48         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 36.26/36.48             (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 36.26/36.48          | ((X2) = (X0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['71', '72'])).
% 36.26/36.48  thf('74', plain,
% 36.26/36.48      ((((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_D_2) = (k1_xboole_0))
% 36.26/36.48        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['70', '73'])).
% 36.26/36.48  thf('75', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('76', plain, (((sk_B_1) = (k1_xboole_0))),
% 36.26/36.48      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 36.26/36.48  thf('77', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (k1_xboole_0))),
% 36.26/36.48      inference('demod', [status(thm)], ['75', '76'])).
% 36.26/36.48  thf('78', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 36.26/36.48      inference('simplify_reflect-', [status(thm)], ['74', '77'])).
% 36.26/36.48  thf('79', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 36.26/36.48      inference('simplify_reflect-', [status(thm)], ['74', '77'])).
% 36.26/36.48  thf('80', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.26/36.48         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 36.26/36.48      inference('sup+', [status(thm)], ['40', '41'])).
% 36.26/36.48  thf('81', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 36.26/36.48         ((r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 36.26/36.48          | ((X25) = (k1_xboole_0))
% 36.26/36.48          | ((X25) != (k1_funct_1 @ X24 @ X23))
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | ~ (v1_relat_1 @ X24))),
% 36.26/36.48      inference('cnf', [status(esa)], [d4_funct_1])).
% 36.26/36.48  thf('82', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i]:
% 36.26/36.48         (~ (v1_relat_1 @ X24)
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | ((k1_funct_1 @ X24 @ X23) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['81'])).
% 36.26/36.48  thf('83', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i]:
% 36.26/36.48         (~ (v1_relat_1 @ X24)
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 36.26/36.48          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['27'])).
% 36.26/36.48  thf('84', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i]:
% 36.26/36.48         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 36.26/36.48          | ~ (v1_funct_1 @ X0)
% 36.26/36.48          | ~ (v1_relat_1 @ X0)
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 36.26/36.48          | ~ (v1_funct_1 @ X0)
% 36.26/36.48          | ~ (v1_relat_1 @ X0))),
% 36.26/36.48      inference('sup-', [status(thm)], ['82', '83'])).
% 36.26/36.48  thf('85', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i]:
% 36.26/36.48         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 36.26/36.48          | ~ (v1_relat_1 @ X0)
% 36.26/36.48          | ~ (v1_funct_1 @ X0)
% 36.26/36.48          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['84'])).
% 36.26/36.48  thf('86', plain,
% 36.26/36.48      (![X27 : $i, X28 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 36.26/36.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.26/36.48  thf('87', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i]:
% 36.26/36.48         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 36.26/36.48          | ~ (v1_funct_1 @ X0)
% 36.26/36.48          | ~ (v1_relat_1 @ X0)
% 36.26/36.48          | ~ (r1_tarski @ X0 @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1))))),
% 36.26/36.48      inference('sup-', [status(thm)], ['85', '86'])).
% 36.26/36.48  thf('88', plain,
% 36.26/36.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.26/36.48         ((zip_tseitin_0 @ X1 @ X2)
% 36.26/36.48          | ~ (v1_relat_1 @ X1)
% 36.26/36.48          | ~ (v1_funct_1 @ X1)
% 36.26/36.48          | ((k1_funct_1 @ X1 @ X0) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['80', '87'])).
% 36.26/36.48  thf('89', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (k1_xboole_0))),
% 36.26/36.48      inference('demod', [status(thm)], ['75', '76'])).
% 36.26/36.48  thf('90', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (((k1_xboole_0) != (k1_xboole_0))
% 36.26/36.48          | ~ (v1_funct_1 @ sk_D_2)
% 36.26/36.48          | ~ (v1_relat_1 @ sk_D_2)
% 36.26/36.48          | (zip_tseitin_0 @ sk_D_2 @ X0))),
% 36.26/36.48      inference('sup-', [status(thm)], ['88', '89'])).
% 36.26/36.48  thf('91', plain, ((v1_funct_1 @ sk_D_2)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('92', plain, ((v1_relat_1 @ sk_D_2)),
% 36.26/36.48      inference('sup-', [status(thm)], ['31', '32'])).
% 36.26/36.48  thf('93', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ sk_D_2 @ X0))),
% 36.26/36.48      inference('demod', [status(thm)], ['90', '91', '92'])).
% 36.26/36.48  thf('94', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_D_2 @ X0)),
% 36.26/36.48      inference('simplify', [status(thm)], ['93'])).
% 36.26/36.48  thf('95', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['79', '94'])).
% 36.26/36.48  thf('96', plain,
% 36.26/36.48      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['8', '15'])).
% 36.26/36.48  thf('97', plain,
% 36.26/36.48      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 36.26/36.48      inference('sup-', [status(thm)], ['5', '6'])).
% 36.26/36.48  thf('98', plain,
% 36.26/36.48      ((~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2))
% 36.26/36.48        | (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 36.26/36.48      inference('sup-', [status(thm)], ['96', '97'])).
% 36.26/36.48  thf('99', plain,
% 36.26/36.48      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 36.26/36.48        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('demod', [status(thm)], ['11', '14'])).
% 36.26/36.48  thf('100', plain,
% 36.26/36.48      ((((sk_A) = (k1_relat_1 @ sk_D_2))
% 36.26/36.48        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 36.26/36.48      inference('clc', [status(thm)], ['98', '99'])).
% 36.26/36.48  thf('101', plain,
% 36.26/36.48      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['95', '100'])).
% 36.26/36.48  thf('102', plain,
% 36.26/36.48      ((((sk_A) = (k1_relat_1 @ k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['78', '101'])).
% 36.26/36.48  thf('103', plain,
% 36.26/36.48      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ k1_xboole_0)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['102'])).
% 36.26/36.48  thf('104', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 36.26/36.48      inference('simplify_reflect-', [status(thm)], ['74', '77'])).
% 36.26/36.48  thf('105', plain, ((v1_funct_1 @ sk_D_2)),
% 36.26/36.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.26/36.48  thf('106', plain, (((v1_funct_1 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['104', '105'])).
% 36.26/36.48  thf('107', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.26/36.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.26/36.48  thf('108', plain,
% 36.26/36.48      (![X35 : $i]:
% 36.26/36.48         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X35) @ X35))),
% 36.26/36.48      inference('cnf', [status(esa)], [t6_mcart_1])).
% 36.26/36.48  thf('109', plain,
% 36.26/36.48      (![X23 : $i, X24 : $i]:
% 36.26/36.48         (~ (v1_relat_1 @ X24)
% 36.26/36.48          | ~ (v1_funct_1 @ X24)
% 36.26/36.48          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 36.26/36.48          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 36.26/36.48      inference('simplify', [status(thm)], ['27'])).
% 36.26/36.48  thf('110', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 36.26/36.48          | (r2_hidden @ 
% 36.26/36.48             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 36.26/36.48              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 36.26/36.48             X0)
% 36.26/36.48          | ~ (v1_funct_1 @ X0)
% 36.26/36.48          | ~ (v1_relat_1 @ X0))),
% 36.26/36.48      inference('sup-', [status(thm)], ['108', '109'])).
% 36.26/36.48  thf('111', plain,
% 36.26/36.48      (![X27 : $i, X28 : $i]:
% 36.26/36.48         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 36.26/36.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 36.26/36.48  thf('112', plain,
% 36.26/36.48      (![X0 : $i]:
% 36.26/36.48         (~ (v1_relat_1 @ X0)
% 36.26/36.48          | ~ (v1_funct_1 @ X0)
% 36.26/36.48          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 36.26/36.48          | ~ (r1_tarski @ X0 @ 
% 36.26/36.48               (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 36.26/36.48                (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))))))),
% 36.26/36.48      inference('sup-', [status(thm)], ['110', '111'])).
% 36.26/36.48  thf('113', plain,
% 36.26/36.48      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 36.26/36.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 36.26/36.48        | ~ (v1_relat_1 @ k1_xboole_0))),
% 36.26/36.48      inference('sup-', [status(thm)], ['107', '112'])).
% 36.26/36.48  thf('114', plain,
% 36.26/36.48      ((((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 36.26/36.48        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup-', [status(thm)], ['106', '113'])).
% 36.26/36.48  thf('115', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 36.26/36.48      inference('simplify_reflect-', [status(thm)], ['74', '77'])).
% 36.26/36.48  thf('116', plain, ((v1_relat_1 @ sk_D_2)),
% 36.26/36.48      inference('sup-', [status(thm)], ['31', '32'])).
% 36.26/36.48  thf('117', plain, (((v1_relat_1 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['115', '116'])).
% 36.26/36.48  thf('118', plain,
% 36.26/36.48      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 36.26/36.48      inference('clc', [status(thm)], ['114', '117'])).
% 36.26/36.48  thf('119', plain,
% 36.26/36.48      ((((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0))
% 36.26/36.48        | ((sk_A) = (k1_xboole_0)))),
% 36.26/36.48      inference('sup+', [status(thm)], ['103', '118'])).
% 36.26/36.48  thf('120', plain, (((sk_A) = (k1_xboole_0))),
% 36.26/36.48      inference('simplify', [status(thm)], ['119'])).
% 36.26/36.48  thf('121', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 36.26/36.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 36.26/36.48  thf('122', plain, ($false),
% 36.26/36.48      inference('demod', [status(thm)], ['2', '120', '121'])).
% 36.26/36.48  
% 36.26/36.48  % SZS output end Refutation
% 36.26/36.48  
% 36.26/36.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
