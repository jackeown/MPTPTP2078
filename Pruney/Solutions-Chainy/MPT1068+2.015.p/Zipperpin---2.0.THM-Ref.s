%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zpaMru1Luw

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:58 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 169 expanded)
%              Number of leaves         :   40 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          : 1008 (3416 expanded)
%              Number of equality atoms :   64 ( 160 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t185_funct_2,conjecture,(
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
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

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
                          = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t185_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['3','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
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

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['19','28'])).

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

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k1_funct_1 @ X3 @ ( k1_funct_1 @ X4 @ X5 ) ) )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
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

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12 )
        = ( k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X15 @ X13 @ X16 ) @ ( k1_relset_1 @ X13 @ X14 @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X13 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','58','59','60','61'])).

thf('63',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','69'])).

thf('71',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zpaMru1Luw
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:44:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.61/3.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.61/3.80  % Solved by: fo/fo7.sh
% 3.61/3.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.61/3.80  % done 2205 iterations in 3.339s
% 3.61/3.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.61/3.80  % SZS output start Refutation
% 3.61/3.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.61/3.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.61/3.80  thf(sk_A_type, type, sk_A: $i).
% 3.61/3.80  thf(sk_B_type, type, sk_B: $i).
% 3.61/3.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.61/3.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.61/3.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.61/3.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.61/3.80  thf(sk_E_type, type, sk_E: $i).
% 3.61/3.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.61/3.80  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 3.61/3.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.61/3.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.61/3.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.61/3.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.61/3.80  thf(sk_F_type, type, sk_F: $i).
% 3.61/3.80  thf(sk_C_type, type, sk_C: $i).
% 3.61/3.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.61/3.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.61/3.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.61/3.80  thf(sk_D_type, type, sk_D: $i).
% 3.61/3.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.61/3.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.61/3.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.61/3.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.61/3.80  thf(t185_funct_2, conjecture,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.61/3.80       ( ![D:$i]:
% 3.61/3.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.61/3.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.61/3.80           ( ![E:$i]:
% 3.61/3.80             ( ( ( v1_funct_1 @ E ) & 
% 3.61/3.80                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.61/3.80               ( ![F:$i]:
% 3.61/3.80                 ( ( m1_subset_1 @ F @ B ) =>
% 3.61/3.80                   ( ( r1_tarski @
% 3.61/3.80                       ( k2_relset_1 @ B @ C @ D ) @ 
% 3.61/3.80                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.61/3.80                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.61/3.80                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.61/3.80                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.61/3.80  thf(zf_stmt_0, negated_conjecture,
% 3.61/3.80    (~( ![A:$i,B:$i,C:$i]:
% 3.61/3.80        ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.61/3.80          ( ![D:$i]:
% 3.61/3.80            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.61/3.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.61/3.80              ( ![E:$i]:
% 3.61/3.80                ( ( ( v1_funct_1 @ E ) & 
% 3.61/3.80                    ( m1_subset_1 @
% 3.61/3.80                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.61/3.80                  ( ![F:$i]:
% 3.61/3.80                    ( ( m1_subset_1 @ F @ B ) =>
% 3.61/3.80                      ( ( r1_tarski @
% 3.61/3.80                          ( k2_relset_1 @ B @ C @ D ) @ 
% 3.61/3.80                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.61/3.80                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.61/3.80                          ( ( k1_funct_1 @
% 3.61/3.80                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.61/3.80                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.61/3.80    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 3.61/3.80  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(t2_subset, axiom,
% 3.61/3.80    (![A:$i,B:$i]:
% 3.61/3.80     ( ( m1_subset_1 @ A @ B ) =>
% 3.61/3.80       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.61/3.80  thf('2', plain,
% 3.61/3.80      (![X1 : $i, X2 : $i]:
% 3.61/3.80         ((r2_hidden @ X1 @ X2)
% 3.61/3.80          | (v1_xboole_0 @ X2)
% 3.61/3.80          | ~ (m1_subset_1 @ X1 @ X2))),
% 3.61/3.80      inference('cnf', [status(esa)], [t2_subset])).
% 3.61/3.80  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 3.61/3.80      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.80  thf(l13_xboole_0, axiom,
% 3.61/3.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.61/3.80  thf('4', plain,
% 3.61/3.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.61/3.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.61/3.80  thf('5', plain,
% 3.61/3.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.61/3.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.61/3.80  thf('6', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.61/3.80      inference('sup+', [status(thm)], ['4', '5'])).
% 3.61/3.80  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('8', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         (((X0) != (k1_xboole_0))
% 3.61/3.80          | ~ (v1_xboole_0 @ X0)
% 3.61/3.80          | ~ (v1_xboole_0 @ sk_B))),
% 3.61/3.80      inference('sup-', [status(thm)], ['6', '7'])).
% 3.61/3.80  thf('9', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.61/3.80      inference('simplify', [status(thm)], ['8'])).
% 3.61/3.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.61/3.80  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.61/3.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.61/3.80  thf('11', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.61/3.80      inference('simplify_reflect+', [status(thm)], ['9', '10'])).
% 3.61/3.80  thf('12', plain, ((r2_hidden @ sk_F @ sk_B)),
% 3.61/3.80      inference('clc', [status(thm)], ['3', '11'])).
% 3.61/3.80  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(d1_funct_2, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.61/3.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.61/3.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.61/3.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.61/3.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.61/3.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.61/3.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.61/3.80  thf(zf_stmt_1, axiom,
% 3.61/3.80    (![C:$i,B:$i,A:$i]:
% 3.61/3.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.61/3.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.61/3.80  thf('14', plain,
% 3.61/3.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.80         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 3.61/3.80          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 3.61/3.80          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.61/3.80  thf('15', plain,
% 3.61/3.80      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 3.61/3.80        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 3.61/3.80      inference('sup-', [status(thm)], ['13', '14'])).
% 3.61/3.80  thf('16', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(redefinition_k1_relset_1, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.61/3.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.61/3.80  thf('17', plain,
% 3.61/3.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.61/3.80         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 3.61/3.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.61/3.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.61/3.80  thf('18', plain,
% 3.61/3.80      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.61/3.80      inference('sup-', [status(thm)], ['16', '17'])).
% 3.61/3.80  thf('19', plain,
% 3.61/3.80      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 3.61/3.80      inference('demod', [status(thm)], ['15', '18'])).
% 3.61/3.80  thf('20', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.61/3.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.61/3.80  thf(zf_stmt_4, axiom,
% 3.61/3.80    (![B:$i,A:$i]:
% 3.61/3.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.61/3.80       ( zip_tseitin_0 @ B @ A ) ))).
% 3.61/3.80  thf(zf_stmt_5, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.61/3.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.61/3.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.61/3.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.61/3.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.61/3.80  thf('21', plain,
% 3.61/3.80      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.61/3.80         (~ (zip_tseitin_0 @ X22 @ X23)
% 3.61/3.80          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 3.61/3.80          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.61/3.80  thf('22', plain,
% 3.61/3.80      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.61/3.80      inference('sup-', [status(thm)], ['20', '21'])).
% 3.61/3.80  thf('23', plain,
% 3.61/3.80      (![X17 : $i, X18 : $i]:
% 3.61/3.80         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.61/3.80  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.61/3.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.61/3.80  thf('25', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.61/3.80      inference('sup+', [status(thm)], ['23', '24'])).
% 3.61/3.80  thf('26', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('27', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 3.61/3.80      inference('sup-', [status(thm)], ['25', '26'])).
% 3.61/3.80  thf('28', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 3.61/3.80      inference('demod', [status(thm)], ['22', '27'])).
% 3.61/3.80  thf('29', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.61/3.80      inference('demod', [status(thm)], ['19', '28'])).
% 3.61/3.80  thf(t23_funct_1, axiom,
% 3.61/3.80    (![A:$i,B:$i]:
% 3.61/3.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.61/3.80       ( ![C:$i]:
% 3.61/3.80         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.61/3.80           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.61/3.80             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.61/3.80               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 3.61/3.80  thf('30', plain,
% 3.61/3.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.61/3.80         (~ (v1_relat_1 @ X3)
% 3.61/3.80          | ~ (v1_funct_1 @ X3)
% 3.61/3.80          | ((k1_funct_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 3.61/3.80              = (k1_funct_1 @ X3 @ (k1_funct_1 @ X4 @ X5)))
% 3.61/3.80          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 3.61/3.80          | ~ (v1_funct_1 @ X4)
% 3.61/3.80          | ~ (v1_relat_1 @ X4))),
% 3.61/3.80      inference('cnf', [status(esa)], [t23_funct_1])).
% 3.61/3.80  thf('31', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         (~ (r2_hidden @ X0 @ sk_B)
% 3.61/3.80          | ~ (v1_relat_1 @ sk_D)
% 3.61/3.80          | ~ (v1_funct_1 @ sk_D)
% 3.61/3.80          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 3.61/3.80              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 3.61/3.80          | ~ (v1_funct_1 @ X1)
% 3.61/3.80          | ~ (v1_relat_1 @ X1))),
% 3.61/3.80      inference('sup-', [status(thm)], ['29', '30'])).
% 3.61/3.80  thf('32', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(cc1_relset_1, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.61/3.80       ( v1_relat_1 @ C ) ))).
% 3.61/3.80  thf('33', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.61/3.80         ((v1_relat_1 @ X6)
% 3.61/3.80          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.61/3.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.61/3.80  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 3.61/3.80      inference('sup-', [status(thm)], ['32', '33'])).
% 3.61/3.80  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('36', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         (~ (r2_hidden @ X0 @ sk_B)
% 3.61/3.80          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 3.61/3.80              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 3.61/3.80          | ~ (v1_funct_1 @ X1)
% 3.61/3.80          | ~ (v1_relat_1 @ X1))),
% 3.61/3.80      inference('demod', [status(thm)], ['31', '34', '35'])).
% 3.61/3.80  thf('37', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         (~ (v1_relat_1 @ X0)
% 3.61/3.80          | ~ (v1_funct_1 @ X0)
% 3.61/3.80          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 3.61/3.80              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F))))),
% 3.61/3.80      inference('sup-', [status(thm)], ['12', '36'])).
% 3.61/3.80  thf('38', plain,
% 3.61/3.80      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 3.61/3.80        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('39', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('40', plain,
% 3.61/3.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.61/3.80         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 3.61/3.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.61/3.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.61/3.80  thf('41', plain,
% 3.61/3.80      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.61/3.80      inference('sup-', [status(thm)], ['39', '40'])).
% 3.61/3.80  thf('42', plain,
% 3.61/3.80      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 3.61/3.80      inference('demod', [status(thm)], ['38', '41'])).
% 3.61/3.80  thf('43', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(d12_funct_2, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i,D:$i]:
% 3.61/3.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.61/3.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.61/3.80       ( ![E:$i]:
% 3.61/3.80         ( ( ( v1_funct_1 @ E ) & 
% 3.61/3.80             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.61/3.80           ( ( r1_tarski @
% 3.61/3.80               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 3.61/3.80             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.61/3.80               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 3.61/3.80                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 3.61/3.80  thf('44', plain,
% 3.61/3.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.61/3.80         (~ (v1_funct_1 @ X12)
% 3.61/3.80          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 3.61/3.80          | ((k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12)
% 3.61/3.80              = (k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12))
% 3.61/3.80          | ~ (r1_tarski @ (k2_relset_1 @ X15 @ X13 @ X16) @ 
% 3.61/3.80               (k1_relset_1 @ X13 @ X14 @ X12))
% 3.61/3.80          | ((X13) = (k1_xboole_0))
% 3.61/3.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 3.61/3.80          | ~ (v1_funct_2 @ X16 @ X15 @ X13)
% 3.61/3.80          | ~ (v1_funct_1 @ X16))),
% 3.61/3.80      inference('cnf', [status(esa)], [d12_funct_2])).
% 3.61/3.80  thf('45', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         (~ (v1_funct_1 @ X0)
% 3.61/3.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 3.61/3.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 3.61/3.80          | ((sk_C) = (k1_xboole_0))
% 3.61/3.80          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 3.61/3.80               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 3.61/3.80          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 3.61/3.80              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 3.61/3.80          | ~ (v1_funct_1 @ sk_E))),
% 3.61/3.80      inference('sup-', [status(thm)], ['43', '44'])).
% 3.61/3.80  thf('46', plain,
% 3.61/3.80      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.61/3.80      inference('sup-', [status(thm)], ['39', '40'])).
% 3.61/3.80  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('48', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         (~ (v1_funct_1 @ X0)
% 3.61/3.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 3.61/3.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 3.61/3.80          | ((sk_C) = (k1_xboole_0))
% 3.61/3.80          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 3.61/3.80          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 3.61/3.80              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 3.61/3.80      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.61/3.80  thf('49', plain,
% 3.61/3.80      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.61/3.80          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 3.61/3.80        | ((sk_C) = (k1_xboole_0))
% 3.61/3.80        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 3.61/3.80        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 3.61/3.80        | ~ (v1_funct_1 @ sk_D))),
% 3.61/3.80      inference('sup-', [status(thm)], ['42', '48'])).
% 3.61/3.80  thf('50', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('51', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(redefinition_k1_partfun1, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.61/3.80     ( ( ( v1_funct_1 @ E ) & 
% 3.61/3.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.61/3.80         ( v1_funct_1 @ F ) & 
% 3.61/3.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.61/3.80       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.61/3.80  thf('52', plain,
% 3.61/3.80      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.61/3.80         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.61/3.80          | ~ (v1_funct_1 @ X25)
% 3.61/3.80          | ~ (v1_funct_1 @ X28)
% 3.61/3.80          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.61/3.80          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 3.61/3.80              = (k5_relat_1 @ X25 @ X28)))),
% 3.61/3.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.61/3.80  thf('53', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 3.61/3.80            = (k5_relat_1 @ sk_D @ X0))
% 3.61/3.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.61/3.80          | ~ (v1_funct_1 @ X0)
% 3.61/3.80          | ~ (v1_funct_1 @ sk_D))),
% 3.61/3.80      inference('sup-', [status(thm)], ['51', '52'])).
% 3.61/3.80  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('55', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 3.61/3.80            = (k5_relat_1 @ sk_D @ X0))
% 3.61/3.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.61/3.80          | ~ (v1_funct_1 @ X0))),
% 3.61/3.80      inference('demod', [status(thm)], ['53', '54'])).
% 3.61/3.80  thf('56', plain,
% 3.61/3.80      ((~ (v1_funct_1 @ sk_E)
% 3.61/3.80        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.61/3.80            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.61/3.80      inference('sup-', [status(thm)], ['50', '55'])).
% 3.61/3.80  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('58', plain,
% 3.61/3.80      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.61/3.80         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.61/3.80      inference('demod', [status(thm)], ['56', '57'])).
% 3.61/3.80  thf('59', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('62', plain,
% 3.61/3.80      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.61/3.80          = (k5_relat_1 @ sk_D @ sk_E))
% 3.61/3.80        | ((sk_C) = (k1_xboole_0)))),
% 3.61/3.80      inference('demod', [status(thm)], ['49', '58', '59', '60', '61'])).
% 3.61/3.80  thf('63', plain,
% 3.61/3.80      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 3.61/3.80         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('64', plain,
% 3.61/3.80      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.61/3.80          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 3.61/3.80        | ((sk_C) = (k1_xboole_0)))),
% 3.61/3.80      inference('sup-', [status(thm)], ['62', '63'])).
% 3.61/3.80  thf('65', plain,
% 3.61/3.80      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.61/3.80          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 3.61/3.80        | ~ (v1_funct_1 @ sk_E)
% 3.61/3.80        | ~ (v1_relat_1 @ sk_E)
% 3.61/3.80        | ((sk_C) = (k1_xboole_0)))),
% 3.61/3.80      inference('sup-', [status(thm)], ['37', '64'])).
% 3.61/3.80  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('67', plain,
% 3.61/3.80      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('68', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.61/3.80         ((v1_relat_1 @ X6)
% 3.61/3.80          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.61/3.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.61/3.80  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 3.61/3.80      inference('sup-', [status(thm)], ['67', '68'])).
% 3.61/3.80  thf('70', plain,
% 3.61/3.80      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.61/3.80          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 3.61/3.80        | ((sk_C) = (k1_xboole_0)))),
% 3.61/3.80      inference('demod', [status(thm)], ['65', '66', '69'])).
% 3.61/3.80  thf('71', plain, (((sk_C) = (k1_xboole_0))),
% 3.61/3.80      inference('simplify', [status(thm)], ['70'])).
% 3.61/3.80  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.61/3.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.61/3.80  thf('73', plain, ($false),
% 3.61/3.80      inference('demod', [status(thm)], ['0', '71', '72'])).
% 3.61/3.80  
% 3.61/3.80  % SZS output end Refutation
% 3.61/3.80  
% 3.61/3.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
