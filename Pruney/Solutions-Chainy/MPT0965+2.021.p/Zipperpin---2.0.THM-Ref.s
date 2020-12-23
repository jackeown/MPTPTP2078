%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6FF79Ehb1w

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:00 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 129 expanded)
%              Number of leaves         :   46 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  651 (1133 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('9',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','13','16'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X29 @ X28 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','27'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X37: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X37 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X37: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X37 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ ( k6_subset_1 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference('sup-',[status(thm)],['32','53'])).

thf('55',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6FF79Ehb1w
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:53:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 99 iterations in 0.053s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.34/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.34/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(t7_funct_2, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.34/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.34/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.34/0.53            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53          ( ( r2_hidden @ C @ A ) =>
% 0.34/0.53            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc2_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.34/0.53         ((v5_relat_1 @ X31 @ X33)
% 0.34/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.53  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.34/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.53  thf('3', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(d1_funct_2, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.34/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.34/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_1, axiom,
% 0.34/0.53    (![C:$i,B:$i,A:$i]:
% 0.34/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.34/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.34/0.53         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.34/0.53          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.34/0.53          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.34/0.53        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.53  thf(zf_stmt_2, axiom,
% 0.34/0.53    (![B:$i,A:$i]:
% 0.34/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X43 : $i, X44 : $i]:
% 0.34/0.53         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.34/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.34/0.53  thf(zf_stmt_5, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.34/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.34/0.53         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.34/0.53          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.34/0.53          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '10'])).
% 0.34/0.53  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('13', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.34/0.53         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.34/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.34/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf('17', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.34/0.53      inference('demod', [status(thm)], ['6', '13', '16'])).
% 0.34/0.53  thf(t176_funct_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.53       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.34/0.53         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.34/0.53          | (m1_subset_1 @ (k1_funct_1 @ X29 @ X28) @ X30)
% 0.34/0.53          | ~ (v1_funct_1 @ X29)
% 0.34/0.53          | ~ (v5_relat_1 @ X29 @ X30)
% 0.34/0.53          | ~ (v1_relat_1 @ X29))),
% 0.34/0.53      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.34/0.53          | ~ (v1_relat_1 @ sk_D)
% 0.34/0.53          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.34/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.34/0.53          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc2_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.34/0.53          | (v1_relat_1 @ X22)
% 0.34/0.53          | ~ (v1_relat_1 @ X23))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.34/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf(fc6_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.53  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.34/0.53          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.34/0.53          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.34/0.53      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ X0)
% 0.34/0.53          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '26'])).
% 0.34/0.53  thf('28', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.34/0.53      inference('sup-', [status(thm)], ['2', '27'])).
% 0.34/0.53  thf(t2_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.34/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      (![X17 : $i, X18 : $i]:
% 0.34/0.53         ((r2_hidden @ X17 @ X18)
% 0.34/0.53          | (v1_xboole_0 @ X18)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.34/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.34/0.53        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.53  thf('31', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('32', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.34/0.53      inference('clc', [status(thm)], ['30', '31'])).
% 0.34/0.53  thf(t6_mcart_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.34/0.53                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.34/0.53                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.34/0.53                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.34/0.53                       ( r2_hidden @ G @ B ) ) =>
% 0.34/0.53                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (![X37 : $i]:
% 0.34/0.53         (((X37) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X37) @ X37))),
% 0.34/0.53      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.34/0.53  thf(dt_k6_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (![X13 : $i, X14 : $i]:
% 0.34/0.53         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.34/0.53  thf(t5_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.34/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X19 @ X20)
% 0.34/0.53          | ~ (v1_xboole_0 @ X21)
% 0.34/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['33', '36'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X37 : $i]:
% 0.34/0.53         (((X37) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X37) @ X37))),
% 0.34/0.53      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.34/0.53  thf(t48_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.34/0.53           = (k3_xboole_0 @ X8 @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.34/0.53  thf(redefinition_k6_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i]:
% 0.34/0.53         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.34/0.53  thf('41', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i]:
% 0.34/0.53         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]:
% 0.34/0.53         ((k6_subset_1 @ X8 @ (k6_subset_1 @ X8 @ X9))
% 0.34/0.53           = (k3_xboole_0 @ X8 @ X9))),
% 0.34/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['38', '44'])).
% 0.34/0.53  thf(t100_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.34/0.53  thf('46', plain,
% 0.34/0.53      (![X2 : $i, X3 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X2 @ X3)
% 0.34/0.53           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i]:
% 0.34/0.53         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.34/0.53  thf('48', plain,
% 0.34/0.53      (![X2 : $i, X3 : $i]:
% 0.34/0.53         ((k6_subset_1 @ X2 @ X3)
% 0.34/0.53           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.34/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.34/0.53  thf('49', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((k6_subset_1 @ X1 @ X0) = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.34/0.53          | ~ (v1_xboole_0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['45', '48'])).
% 0.34/0.53  thf(t5_boole, axiom,
% 0.34/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.53  thf('50', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.34/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.34/0.53  thf('51', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((k6_subset_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.34/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.34/0.53  thf('52', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['37', '51'])).
% 0.34/0.53  thf('53', plain,
% 0.34/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['52'])).
% 0.34/0.53  thf('54', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['32', '53'])).
% 0.34/0.53  thf('55', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('56', plain, ($false),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
