%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pb7WLK41bc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:07 EST 2020

% Result     : Theorem 21.08s
% Output     : Refutation 21.08s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 346 expanded)
%              Number of leaves         :   53 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          : 1405 (6237 expanded)
%              Number of equality atoms :   77 ( 269 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['9','14'])).

thf('16',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference(clc,[status(thm)],['3','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
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
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ( X56
        = ( k1_relset_1 @ X56 @ X57 @ X58 ) )
      | ~ ( zip_tseitin_1 @ X58 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X44 @ X45 @ X43 )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( zip_tseitin_0 @ X59 @ X60 )
      | ( zip_tseitin_1 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X54 @ X55 )
      | ( X54 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('28',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','34'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X33 @ X32 ) @ X34 )
        = ( k1_funct_1 @ X32 @ ( k1_funct_1 @ X33 @ X34 ) ) )
      | ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['16','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k2_relset_1 @ X47 @ X48 @ X46 )
        = ( k2_relat_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k8_funct_2 @ X52 @ X50 @ X51 @ X53 @ X49 )
        = ( k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X52 @ X50 @ X53 ) @ ( k1_relset_1 @ X50 @ X51 @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X50 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X44 @ X45 @ X43 )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['51','54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
    | ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('62',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','62','63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('69',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) )
      | ( ( k1_partfun1 @ X66 @ X67 @ X69 @ X70 @ X65 @ X68 )
        = ( k5_relat_1 @ X65 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('77',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v5_relat_1 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference(clc,[status(thm)],['3','15'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('83',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('86',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','34'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('88',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['81','93'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('95',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( ( k7_partfun1 @ X64 @ X63 @ X62 )
        = ( k1_funct_1 @ X63 @ X62 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v5_relat_1 @ X63 @ X64 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X27: $i,X28: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('101',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['96','101','102'])).

thf('104',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['80','103'])).

thf('105',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['77','104'])).

thf('106',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','105'])).

thf('107',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['99','100'])).

thf('110',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['0','111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pb7WLK41bc
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:42:45 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 21.08/21.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.08/21.34  % Solved by: fo/fo7.sh
% 21.08/21.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.08/21.34  % done 23543 iterations in 20.876s
% 21.08/21.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.08/21.34  % SZS output start Refutation
% 21.08/21.34  thf(sk_B_type, type, sk_B: $i > $i).
% 21.08/21.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 21.08/21.34  thf(sk_F_type, type, sk_F: $i).
% 21.08/21.34  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 21.08/21.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.08/21.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.08/21.34  thf(sk_A_type, type, sk_A: $i).
% 21.08/21.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.08/21.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.08/21.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.08/21.34  thf(sk_D_type, type, sk_D: $i).
% 21.08/21.34  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 21.08/21.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.08/21.34  thf(sk_E_type, type, sk_E: $i).
% 21.08/21.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 21.08/21.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.08/21.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.08/21.34  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 21.08/21.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.08/21.34  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 21.08/21.34  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 21.08/21.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.08/21.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.08/21.34  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 21.08/21.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 21.08/21.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.08/21.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 21.08/21.34  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 21.08/21.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.08/21.34  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 21.08/21.34  thf(t186_funct_2, conjecture,
% 21.08/21.34    (![A:$i,B:$i,C:$i]:
% 21.08/21.34     ( ( ~( v1_xboole_0 @ C ) ) =>
% 21.08/21.34       ( ![D:$i]:
% 21.08/21.34         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 21.08/21.34             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.08/21.34           ( ![E:$i]:
% 21.08/21.34             ( ( ( v1_funct_1 @ E ) & 
% 21.08/21.34                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 21.08/21.34               ( ![F:$i]:
% 21.08/21.34                 ( ( m1_subset_1 @ F @ B ) =>
% 21.08/21.34                   ( ( r1_tarski @
% 21.08/21.34                       ( k2_relset_1 @ B @ C @ D ) @ 
% 21.08/21.34                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 21.08/21.34                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 21.08/21.34                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 21.08/21.34                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 21.08/21.34  thf(zf_stmt_0, negated_conjecture,
% 21.08/21.34    (~( ![A:$i,B:$i,C:$i]:
% 21.08/21.34        ( ( ~( v1_xboole_0 @ C ) ) =>
% 21.08/21.34          ( ![D:$i]:
% 21.08/21.34            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 21.08/21.34                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.08/21.34              ( ![E:$i]:
% 21.08/21.34                ( ( ( v1_funct_1 @ E ) & 
% 21.08/21.34                    ( m1_subset_1 @
% 21.08/21.34                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 21.08/21.34                  ( ![F:$i]:
% 21.08/21.34                    ( ( m1_subset_1 @ F @ B ) =>
% 21.08/21.34                      ( ( r1_tarski @
% 21.08/21.34                          ( k2_relset_1 @ B @ C @ D ) @ 
% 21.08/21.34                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 21.08/21.34                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 21.08/21.34                          ( ( k1_funct_1 @
% 21.08/21.34                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 21.08/21.34                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 21.08/21.34    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 21.08/21.34  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(t2_subset, axiom,
% 21.08/21.34    (![A:$i,B:$i]:
% 21.08/21.34     ( ( m1_subset_1 @ A @ B ) =>
% 21.08/21.34       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 21.08/21.34  thf('2', plain,
% 21.08/21.34      (![X15 : $i, X16 : $i]:
% 21.08/21.34         ((r2_hidden @ X15 @ X16)
% 21.08/21.34          | (v1_xboole_0 @ X16)
% 21.08/21.34          | ~ (m1_subset_1 @ X15 @ X16))),
% 21.08/21.34      inference('cnf', [status(esa)], [t2_subset])).
% 21.08/21.34  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 21.08/21.34      inference('sup-', [status(thm)], ['1', '2'])).
% 21.08/21.34  thf(l13_xboole_0, axiom,
% 21.08/21.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 21.08/21.34  thf('4', plain,
% 21.08/21.34      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 21.08/21.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 21.08/21.34  thf('5', plain,
% 21.08/21.34      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 21.08/21.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 21.08/21.34  thf('6', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 21.08/21.34      inference('sup+', [status(thm)], ['4', '5'])).
% 21.08/21.34  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('8', plain,
% 21.08/21.34      (![X0 : $i]:
% 21.08/21.34         (((X0) != (k1_xboole_0))
% 21.08/21.34          | ~ (v1_xboole_0 @ X0)
% 21.08/21.34          | ~ (v1_xboole_0 @ sk_B_1))),
% 21.08/21.34      inference('sup-', [status(thm)], ['6', '7'])).
% 21.08/21.34  thf('9', plain, ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 21.08/21.34      inference('simplify', [status(thm)], ['8'])).
% 21.08/21.34  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 21.08/21.34  thf('10', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 21.08/21.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.08/21.34  thf(d1_xboole_0, axiom,
% 21.08/21.34    (![A:$i]:
% 21.08/21.34     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 21.08/21.34  thf('11', plain,
% 21.08/21.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 21.08/21.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 21.08/21.34  thf(t7_ordinal1, axiom,
% 21.08/21.34    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 21.08/21.34  thf('12', plain,
% 21.08/21.34      (![X35 : $i, X36 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 21.08/21.34      inference('cnf', [status(esa)], [t7_ordinal1])).
% 21.08/21.34  thf('13', plain,
% 21.08/21.34      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['11', '12'])).
% 21.08/21.34  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 21.08/21.34      inference('sup-', [status(thm)], ['10', '13'])).
% 21.08/21.34  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 21.08/21.34      inference('simplify_reflect+', [status(thm)], ['9', '14'])).
% 21.08/21.34  thf('16', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 21.08/21.34      inference('clc', [status(thm)], ['3', '15'])).
% 21.08/21.34  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(d1_funct_2, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i]:
% 21.08/21.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.08/21.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.08/21.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.08/21.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.08/21.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.08/21.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.08/21.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.08/21.34  thf(zf_stmt_1, axiom,
% 21.08/21.34    (![C:$i,B:$i,A:$i]:
% 21.08/21.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.08/21.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.08/21.34  thf('18', plain,
% 21.08/21.34      (![X56 : $i, X57 : $i, X58 : $i]:
% 21.08/21.34         (~ (v1_funct_2 @ X58 @ X56 @ X57)
% 21.08/21.34          | ((X56) = (k1_relset_1 @ X56 @ X57 @ X58))
% 21.08/21.34          | ~ (zip_tseitin_1 @ X58 @ X57 @ X56))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.08/21.34  thf('19', plain,
% 21.08/21.34      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 21.08/21.34        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['17', '18'])).
% 21.08/21.34  thf('20', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(redefinition_k1_relset_1, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i]:
% 21.08/21.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.08/21.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 21.08/21.34  thf('21', plain,
% 21.08/21.34      (![X43 : $i, X44 : $i, X45 : $i]:
% 21.08/21.34         (((k1_relset_1 @ X44 @ X45 @ X43) = (k1_relat_1 @ X43))
% 21.08/21.34          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 21.08/21.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.08/21.34  thf('22', plain,
% 21.08/21.34      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 21.08/21.34      inference('sup-', [status(thm)], ['20', '21'])).
% 21.08/21.34  thf('23', plain,
% 21.08/21.34      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 21.08/21.34        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 21.08/21.34      inference('demod', [status(thm)], ['19', '22'])).
% 21.08/21.34  thf('24', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.08/21.34  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 21.08/21.34  thf(zf_stmt_4, axiom,
% 21.08/21.34    (![B:$i,A:$i]:
% 21.08/21.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.08/21.34       ( zip_tseitin_0 @ B @ A ) ))).
% 21.08/21.34  thf(zf_stmt_5, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i]:
% 21.08/21.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.08/21.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.08/21.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.08/21.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.08/21.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.08/21.34  thf('25', plain,
% 21.08/21.34      (![X59 : $i, X60 : $i, X61 : $i]:
% 21.08/21.34         (~ (zip_tseitin_0 @ X59 @ X60)
% 21.08/21.34          | (zip_tseitin_1 @ X61 @ X59 @ X60)
% 21.08/21.34          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59))))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.08/21.34  thf('26', plain,
% 21.08/21.34      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 21.08/21.34        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 21.08/21.34      inference('sup-', [status(thm)], ['24', '25'])).
% 21.08/21.34  thf('27', plain,
% 21.08/21.34      (![X54 : $i, X55 : $i]:
% 21.08/21.34         ((zip_tseitin_0 @ X54 @ X55) | ((X54) = (k1_xboole_0)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_4])).
% 21.08/21.34  thf('28', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 21.08/21.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.08/21.34  thf('29', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.08/21.34         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 21.08/21.34      inference('sup+', [status(thm)], ['27', '28'])).
% 21.08/21.34  thf('30', plain,
% 21.08/21.34      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['11', '12'])).
% 21.08/21.34  thf('31', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 21.08/21.34      inference('sup-', [status(thm)], ['29', '30'])).
% 21.08/21.34  thf('32', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('33', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 21.08/21.34      inference('sup-', [status(thm)], ['31', '32'])).
% 21.08/21.34  thf('34', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)),
% 21.08/21.34      inference('demod', [status(thm)], ['26', '33'])).
% 21.08/21.34  thf('35', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 21.08/21.34      inference('demod', [status(thm)], ['23', '34'])).
% 21.08/21.34  thf(t23_funct_1, axiom,
% 21.08/21.34    (![A:$i,B:$i]:
% 21.08/21.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.08/21.34       ( ![C:$i]:
% 21.08/21.34         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 21.08/21.34           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 21.08/21.34             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 21.08/21.34               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 21.08/21.34  thf('36', plain,
% 21.08/21.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 21.08/21.34         (~ (v1_relat_1 @ X32)
% 21.08/21.34          | ~ (v1_funct_1 @ X32)
% 21.08/21.34          | ((k1_funct_1 @ (k5_relat_1 @ X33 @ X32) @ X34)
% 21.08/21.34              = (k1_funct_1 @ X32 @ (k1_funct_1 @ X33 @ X34)))
% 21.08/21.34          | ~ (r2_hidden @ X34 @ (k1_relat_1 @ X33))
% 21.08/21.34          | ~ (v1_funct_1 @ X33)
% 21.08/21.34          | ~ (v1_relat_1 @ X33))),
% 21.08/21.34      inference('cnf', [status(esa)], [t23_funct_1])).
% 21.08/21.34  thf('37', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X0 @ sk_B_1)
% 21.08/21.34          | ~ (v1_relat_1 @ sk_D)
% 21.08/21.34          | ~ (v1_funct_1 @ sk_D)
% 21.08/21.34          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 21.08/21.34              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 21.08/21.34          | ~ (v1_funct_1 @ X1)
% 21.08/21.34          | ~ (v1_relat_1 @ X1))),
% 21.08/21.34      inference('sup-', [status(thm)], ['35', '36'])).
% 21.08/21.34  thf('38', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(cc2_relat_1, axiom,
% 21.08/21.34    (![A:$i]:
% 21.08/21.34     ( ( v1_relat_1 @ A ) =>
% 21.08/21.34       ( ![B:$i]:
% 21.08/21.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 21.08/21.34  thf('39', plain,
% 21.08/21.34      (![X20 : $i, X21 : $i]:
% 21.08/21.34         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 21.08/21.34          | (v1_relat_1 @ X20)
% 21.08/21.34          | ~ (v1_relat_1 @ X21))),
% 21.08/21.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 21.08/21.34  thf('40', plain,
% 21.08/21.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)) | (v1_relat_1 @ sk_D))),
% 21.08/21.34      inference('sup-', [status(thm)], ['38', '39'])).
% 21.08/21.34  thf(fc6_relat_1, axiom,
% 21.08/21.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 21.08/21.34  thf('41', plain,
% 21.08/21.34      (![X27 : $i, X28 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X27 @ X28))),
% 21.08/21.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.08/21.34  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 21.08/21.34      inference('demod', [status(thm)], ['40', '41'])).
% 21.08/21.34  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('44', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X0 @ sk_B_1)
% 21.08/21.34          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 21.08/21.34              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 21.08/21.34          | ~ (v1_funct_1 @ X1)
% 21.08/21.34          | ~ (v1_relat_1 @ X1))),
% 21.08/21.34      inference('demod', [status(thm)], ['37', '42', '43'])).
% 21.08/21.34  thf('45', plain,
% 21.08/21.34      (![X0 : $i]:
% 21.08/21.34         (~ (v1_relat_1 @ X0)
% 21.08/21.34          | ~ (v1_funct_1 @ X0)
% 21.08/21.34          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 21.08/21.34              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F))))),
% 21.08/21.34      inference('sup-', [status(thm)], ['16', '44'])).
% 21.08/21.34  thf('46', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(redefinition_k2_relset_1, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i]:
% 21.08/21.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.08/21.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 21.08/21.34  thf('47', plain,
% 21.08/21.34      (![X46 : $i, X47 : $i, X48 : $i]:
% 21.08/21.34         (((k2_relset_1 @ X47 @ X48 @ X46) = (k2_relat_1 @ X46))
% 21.08/21.34          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 21.08/21.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.08/21.34  thf('48', plain,
% 21.08/21.34      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 21.08/21.34      inference('sup-', [status(thm)], ['46', '47'])).
% 21.08/21.34  thf('49', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(d12_funct_2, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i,D:$i]:
% 21.08/21.34     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.08/21.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.08/21.34       ( ![E:$i]:
% 21.08/21.34         ( ( ( v1_funct_1 @ E ) & 
% 21.08/21.34             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.08/21.34           ( ( r1_tarski @
% 21.08/21.34               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 21.08/21.34             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 21.08/21.34               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 21.08/21.34                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 21.08/21.34  thf('50', plain,
% 21.08/21.34      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 21.08/21.34         (~ (v1_funct_1 @ X49)
% 21.08/21.34          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 21.08/21.34          | ((k8_funct_2 @ X52 @ X50 @ X51 @ X53 @ X49)
% 21.08/21.34              = (k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49))
% 21.08/21.34          | ~ (r1_tarski @ (k2_relset_1 @ X52 @ X50 @ X53) @ 
% 21.08/21.34               (k1_relset_1 @ X50 @ X51 @ X49))
% 21.08/21.34          | ((X50) = (k1_xboole_0))
% 21.08/21.34          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 21.08/21.34          | ~ (v1_funct_2 @ X53 @ X52 @ X50)
% 21.08/21.34          | ~ (v1_funct_1 @ X53))),
% 21.08/21.34      inference('cnf', [status(esa)], [d12_funct_2])).
% 21.08/21.34  thf('51', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (~ (v1_funct_1 @ X0)
% 21.08/21.34          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 21.08/21.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 21.08/21.34          | ((sk_C_1) = (k1_xboole_0))
% 21.08/21.34          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 21.08/21.34               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 21.08/21.34          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 21.08/21.34              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E))
% 21.08/21.34          | ~ (v1_funct_1 @ sk_E))),
% 21.08/21.34      inference('sup-', [status(thm)], ['49', '50'])).
% 21.08/21.34  thf('52', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('53', plain,
% 21.08/21.34      (![X43 : $i, X44 : $i, X45 : $i]:
% 21.08/21.34         (((k1_relset_1 @ X44 @ X45 @ X43) = (k1_relat_1 @ X43))
% 21.08/21.34          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 21.08/21.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.08/21.34  thf('54', plain,
% 21.08/21.34      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('sup-', [status(thm)], ['52', '53'])).
% 21.08/21.34  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('56', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (~ (v1_funct_1 @ X0)
% 21.08/21.34          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 21.08/21.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 21.08/21.34          | ((sk_C_1) = (k1_xboole_0))
% 21.08/21.34          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 21.08/21.34               (k1_relat_1 @ sk_E))
% 21.08/21.34          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 21.08/21.34              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E)))),
% 21.08/21.34      inference('demod', [status(thm)], ['51', '54', '55'])).
% 21.08/21.34  thf('57', plain,
% 21.08/21.34      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 21.08/21.34        | ((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 21.08/21.34            = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 21.08/21.34        | ((sk_C_1) = (k1_xboole_0))
% 21.08/21.34        | ~ (m1_subset_1 @ sk_D @ 
% 21.08/21.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))
% 21.08/21.34        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 21.08/21.34        | ~ (v1_funct_1 @ sk_D))),
% 21.08/21.34      inference('sup-', [status(thm)], ['48', '56'])).
% 21.08/21.34  thf('58', plain,
% 21.08/21.34      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 21.08/21.34        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('59', plain,
% 21.08/21.34      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('sup-', [status(thm)], ['52', '53'])).
% 21.08/21.34  thf('60', plain,
% 21.08/21.34      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 21.08/21.34        (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('demod', [status(thm)], ['58', '59'])).
% 21.08/21.34  thf('61', plain,
% 21.08/21.34      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 21.08/21.34      inference('sup-', [status(thm)], ['46', '47'])).
% 21.08/21.34  thf('62', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('demod', [status(thm)], ['60', '61'])).
% 21.08/21.34  thf('63', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('64', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('66', plain,
% 21.08/21.34      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 21.08/21.34          = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 21.08/21.34        | ((sk_C_1) = (k1_xboole_0)))),
% 21.08/21.34      inference('demod', [status(thm)], ['57', '62', '63', '64', '65'])).
% 21.08/21.34  thf('67', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('68', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(redefinition_k1_partfun1, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 21.08/21.34     ( ( ( v1_funct_1 @ E ) & 
% 21.08/21.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.08/21.34         ( v1_funct_1 @ F ) & 
% 21.08/21.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 21.08/21.34       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 21.08/21.34  thf('69', plain,
% 21.08/21.34      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 21.08/21.34         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67)))
% 21.08/21.34          | ~ (v1_funct_1 @ X65)
% 21.08/21.34          | ~ (v1_funct_1 @ X68)
% 21.08/21.34          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70)))
% 21.08/21.34          | ((k1_partfun1 @ X66 @ X67 @ X69 @ X70 @ X65 @ X68)
% 21.08/21.34              = (k5_relat_1 @ X65 @ X68)))),
% 21.08/21.34      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 21.08/21.34  thf('70', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.08/21.34         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 21.08/21.34            = (k5_relat_1 @ sk_D @ X0))
% 21.08/21.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 21.08/21.34          | ~ (v1_funct_1 @ X0)
% 21.08/21.34          | ~ (v1_funct_1 @ sk_D))),
% 21.08/21.34      inference('sup-', [status(thm)], ['68', '69'])).
% 21.08/21.34  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('72', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.08/21.34         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 21.08/21.34            = (k5_relat_1 @ sk_D @ X0))
% 21.08/21.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 21.08/21.34          | ~ (v1_funct_1 @ X0))),
% 21.08/21.34      inference('demod', [status(thm)], ['70', '71'])).
% 21.08/21.34  thf('73', plain,
% 21.08/21.34      ((~ (v1_funct_1 @ sk_E)
% 21.08/21.34        | ((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 21.08/21.34            = (k5_relat_1 @ sk_D @ sk_E)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['67', '72'])).
% 21.08/21.34  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('75', plain,
% 21.08/21.34      (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 21.08/21.34         = (k5_relat_1 @ sk_D @ sk_E))),
% 21.08/21.34      inference('demod', [status(thm)], ['73', '74'])).
% 21.08/21.34  thf('76', plain,
% 21.08/21.34      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 21.08/21.34          = (k5_relat_1 @ sk_D @ sk_E))
% 21.08/21.34        | ((sk_C_1) = (k1_xboole_0)))),
% 21.08/21.34      inference('sup+', [status(thm)], ['66', '75'])).
% 21.08/21.34  thf('77', plain,
% 21.08/21.34      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 21.08/21.34         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('78', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf(cc2_relset_1, axiom,
% 21.08/21.34    (![A:$i,B:$i,C:$i]:
% 21.08/21.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.08/21.34       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 21.08/21.34  thf('79', plain,
% 21.08/21.34      (![X37 : $i, X38 : $i, X39 : $i]:
% 21.08/21.34         ((v5_relat_1 @ X37 @ X39)
% 21.08/21.34          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 21.08/21.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 21.08/21.34  thf('80', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 21.08/21.34      inference('sup-', [status(thm)], ['78', '79'])).
% 21.08/21.34  thf('81', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 21.08/21.34      inference('clc', [status(thm)], ['3', '15'])).
% 21.08/21.34  thf('82', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('demod', [status(thm)], ['60', '61'])).
% 21.08/21.34  thf(d19_relat_1, axiom,
% 21.08/21.34    (![A:$i,B:$i]:
% 21.08/21.34     ( ( v1_relat_1 @ B ) =>
% 21.08/21.34       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 21.08/21.34  thf('83', plain,
% 21.08/21.34      (![X24 : $i, X25 : $i]:
% 21.08/21.34         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 21.08/21.34          | (v5_relat_1 @ X24 @ X25)
% 21.08/21.34          | ~ (v1_relat_1 @ X24))),
% 21.08/21.34      inference('cnf', [status(esa)], [d19_relat_1])).
% 21.08/21.34  thf('84', plain,
% 21.08/21.34      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['82', '83'])).
% 21.08/21.34  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 21.08/21.34      inference('demod', [status(thm)], ['40', '41'])).
% 21.08/21.34  thf('86', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('demod', [status(thm)], ['84', '85'])).
% 21.08/21.34  thf('87', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 21.08/21.34      inference('demod', [status(thm)], ['23', '34'])).
% 21.08/21.34  thf(t172_funct_1, axiom,
% 21.08/21.34    (![A:$i,B:$i]:
% 21.08/21.34     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 21.08/21.34       ( ![C:$i]:
% 21.08/21.34         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 21.08/21.34           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 21.08/21.34  thf('88', plain,
% 21.08/21.34      (![X29 : $i, X30 : $i, X31 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 21.08/21.34          | (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ X31)
% 21.08/21.34          | ~ (v1_funct_1 @ X30)
% 21.08/21.34          | ~ (v5_relat_1 @ X30 @ X31)
% 21.08/21.34          | ~ (v1_relat_1 @ X30))),
% 21.08/21.34      inference('cnf', [status(esa)], [t172_funct_1])).
% 21.08/21.34  thf('89', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X0 @ sk_B_1)
% 21.08/21.34          | ~ (v1_relat_1 @ sk_D)
% 21.08/21.34          | ~ (v5_relat_1 @ sk_D @ X1)
% 21.08/21.34          | ~ (v1_funct_1 @ sk_D)
% 21.08/21.34          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 21.08/21.34      inference('sup-', [status(thm)], ['87', '88'])).
% 21.08/21.34  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 21.08/21.34      inference('demod', [status(thm)], ['40', '41'])).
% 21.08/21.34  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('92', plain,
% 21.08/21.34      (![X0 : $i, X1 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X0 @ sk_B_1)
% 21.08/21.34          | ~ (v5_relat_1 @ sk_D @ X1)
% 21.08/21.34          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 21.08/21.34      inference('demod', [status(thm)], ['89', '90', '91'])).
% 21.08/21.34  thf('93', plain,
% 21.08/21.34      (![X0 : $i]:
% 21.08/21.34         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 21.08/21.34          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 21.08/21.34      inference('sup-', [status(thm)], ['86', '92'])).
% 21.08/21.34  thf('94', plain,
% 21.08/21.34      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 21.08/21.34      inference('sup-', [status(thm)], ['81', '93'])).
% 21.08/21.34  thf(d8_partfun1, axiom,
% 21.08/21.34    (![A:$i,B:$i]:
% 21.08/21.34     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 21.08/21.34       ( ![C:$i]:
% 21.08/21.34         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 21.08/21.34           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 21.08/21.34  thf('95', plain,
% 21.08/21.34      (![X62 : $i, X63 : $i, X64 : $i]:
% 21.08/21.34         (~ (r2_hidden @ X62 @ (k1_relat_1 @ X63))
% 21.08/21.34          | ((k7_partfun1 @ X64 @ X63 @ X62) = (k1_funct_1 @ X63 @ X62))
% 21.08/21.34          | ~ (v1_funct_1 @ X63)
% 21.08/21.34          | ~ (v5_relat_1 @ X63 @ X64)
% 21.08/21.34          | ~ (v1_relat_1 @ X63))),
% 21.08/21.34      inference('cnf', [status(esa)], [d8_partfun1])).
% 21.08/21.34  thf('96', plain,
% 21.08/21.34      (![X0 : $i]:
% 21.08/21.34         (~ (v1_relat_1 @ sk_E)
% 21.08/21.34          | ~ (v5_relat_1 @ sk_E @ X0)
% 21.08/21.34          | ~ (v1_funct_1 @ sk_E)
% 21.08/21.34          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 21.08/21.34              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 21.08/21.34      inference('sup-', [status(thm)], ['94', '95'])).
% 21.08/21.34  thf('97', plain,
% 21.08/21.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('98', plain,
% 21.08/21.34      (![X20 : $i, X21 : $i]:
% 21.08/21.34         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 21.08/21.34          | (v1_relat_1 @ X20)
% 21.08/21.34          | ~ (v1_relat_1 @ X21))),
% 21.08/21.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 21.08/21.34  thf('99', plain,
% 21.08/21.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 21.08/21.34      inference('sup-', [status(thm)], ['97', '98'])).
% 21.08/21.34  thf('100', plain,
% 21.08/21.34      (![X27 : $i, X28 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X27 @ X28))),
% 21.08/21.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.08/21.34  thf('101', plain, ((v1_relat_1 @ sk_E)),
% 21.08/21.34      inference('demod', [status(thm)], ['99', '100'])).
% 21.08/21.34  thf('102', plain, ((v1_funct_1 @ sk_E)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('103', plain,
% 21.08/21.34      (![X0 : $i]:
% 21.08/21.34         (~ (v5_relat_1 @ sk_E @ X0)
% 21.08/21.34          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 21.08/21.34              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 21.08/21.34      inference('demod', [status(thm)], ['96', '101', '102'])).
% 21.08/21.34  thf('104', plain,
% 21.08/21.34      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 21.08/21.34         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['80', '103'])).
% 21.08/21.34  thf('105', plain,
% 21.08/21.34      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 21.08/21.34         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 21.08/21.34      inference('demod', [status(thm)], ['77', '104'])).
% 21.08/21.34  thf('106', plain,
% 21.08/21.34      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 21.08/21.34          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 21.08/21.34        | ((sk_C_1) = (k1_xboole_0)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['76', '105'])).
% 21.08/21.34  thf('107', plain,
% 21.08/21.34      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 21.08/21.34          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 21.08/21.34        | ~ (v1_funct_1 @ sk_E)
% 21.08/21.34        | ~ (v1_relat_1 @ sk_E)
% 21.08/21.34        | ((sk_C_1) = (k1_xboole_0)))),
% 21.08/21.34      inference('sup-', [status(thm)], ['45', '106'])).
% 21.08/21.34  thf('108', plain, ((v1_funct_1 @ sk_E)),
% 21.08/21.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.08/21.34  thf('109', plain, ((v1_relat_1 @ sk_E)),
% 21.08/21.34      inference('demod', [status(thm)], ['99', '100'])).
% 21.08/21.34  thf('110', plain,
% 21.08/21.34      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 21.08/21.34          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 21.08/21.34        | ((sk_C_1) = (k1_xboole_0)))),
% 21.08/21.34      inference('demod', [status(thm)], ['107', '108', '109'])).
% 21.08/21.34  thf('111', plain, (((sk_C_1) = (k1_xboole_0))),
% 21.08/21.34      inference('simplify', [status(thm)], ['110'])).
% 21.08/21.34  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 21.08/21.34      inference('sup-', [status(thm)], ['10', '13'])).
% 21.08/21.34  thf('113', plain, ($false),
% 21.08/21.34      inference('demod', [status(thm)], ['0', '111', '112'])).
% 21.08/21.34  
% 21.08/21.34  % SZS output end Refutation
% 21.08/21.34  
% 21.08/21.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
