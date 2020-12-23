%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxafGfbHpV

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:59 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 133 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  802 (2671 expanded)
%              Number of equality atoms :   50 ( 127 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('10',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('11',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['9','14'])).

thf('16',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['3','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k1_funct_1 @ X17 @ ( k1_funct_1 @ X18 @ X19 ) ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A_1 ) ) ),
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

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k8_funct_2 @ X9 @ X7 @ X8 @ X10 @ X6 )
        = ( k1_partfun1 @ X9 @ X7 @ X7 @ X8 @ X10 @ X6 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X9 @ X7 @ X10 ) @ ( k1_relset_1 @ X7 @ X8 @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A_1 @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A_1 @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A_1 @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A_1 @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A_1 @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 )
        = ( k5_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A_1 @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A_1 @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A_1 @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','39','40','41','42'])).

thf('44',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A_1 @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','50'])).

thf('52',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxafGfbHpV
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 153 iterations in 0.170s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.67  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(t185_funct_2, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.46/0.67       ( ![D:$i]:
% 0.46/0.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67           ( ![E:$i]:
% 0.46/0.67             ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.67                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.46/0.67               ( ![F:$i]:
% 0.46/0.67                 ( ( m1_subset_1 @ F @ B ) =>
% 0.46/0.67                   ( ( r1_tarski @
% 0.46/0.67                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.46/0.67                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.46/0.67                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.46/0.67                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.67        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.46/0.67          ( ![D:$i]:
% 0.46/0.67            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67              ( ![E:$i]:
% 0.46/0.67                ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.67                    ( m1_subset_1 @
% 0.46/0.67                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.46/0.67                  ( ![F:$i]:
% 0.46/0.67                    ( ( m1_subset_1 @ F @ B ) =>
% 0.46/0.67                      ( ( r1_tarski @
% 0.46/0.67                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.46/0.67                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.46/0.67                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67                          ( ( k1_funct_1 @
% 0.46/0.67                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.46/0.67                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.46/0.67  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t2_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i]:
% 0.46/0.67         ((r2_hidden @ X1 @ X2)
% 0.46/0.67          | (v1_xboole_0 @ X2)
% 0.46/0.67          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.46/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.67  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.67  thf(l13_xboole_0, axiom,
% 0.46/0.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) != (k1_xboole_0))
% 0.46/0.67          | ~ (v1_xboole_0 @ X0)
% 0.46/0.67          | ~ (v1_xboole_0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf('9', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.67  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.46/0.67  thf('10', plain, ((v1_xboole_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.46/0.67  thf('11', plain, ((v1_xboole_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.67  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.67  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.67  thf('15', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.67      inference('simplify_reflect+', [status(thm)], ['9', '14'])).
% 0.46/0.67  thf('16', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.46/0.67      inference('clc', [status(thm)], ['3', '15'])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t21_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( ![E:$i]:
% 0.46/0.67         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.46/0.67           ( ( r2_hidden @ C @ A ) =>
% 0.46/0.67             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.46/0.67                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X17)
% 0.46/0.67          | ~ (v1_funct_1 @ X17)
% 0.46/0.67          | ((k1_funct_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 0.46/0.67              = (k1_funct_1 @ X17 @ (k1_funct_1 @ X18 @ X19)))
% 0.46/0.67          | ((X20) = (k1_xboole_0))
% 0.46/0.67          | ~ (r2_hidden @ X19 @ X21)
% 0.46/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.46/0.67          | ~ (v1_funct_2 @ X18 @ X21 @ X20)
% 0.46/0.67          | ~ (v1_funct_1 @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ sk_D)
% 0.46/0.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.46/0.67          | ~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.46/0.67              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.46/0.67          | ~ (v1_funct_1 @ X1)
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.46/0.67              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.46/0.67          | ~ (v1_funct_1 @ X1)
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.46/0.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['16', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.46/0.67        (k1_relset_1 @ sk_C @ sk_A_1 @ sk_E))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d12_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( ![E:$i]:
% 0.46/0.67         ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.67             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.67           ( ( r1_tarski @
% 0.46/0.67               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.46/0.67             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.46/0.67                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.46/0.67          | ((k8_funct_2 @ X9 @ X7 @ X8 @ X10 @ X6)
% 0.46/0.67              = (k1_partfun1 @ X9 @ X7 @ X7 @ X8 @ X10 @ X6))
% 0.46/0.67          | ~ (r1_tarski @ (k2_relset_1 @ X9 @ X7 @ X10) @ 
% 0.46/0.67               (k1_relset_1 @ X7 @ X8 @ X6))
% 0.46/0.67          | ((X7) = (k1_xboole_0))
% 0.46/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.46/0.67          | ~ (v1_funct_2 @ X10 @ X9 @ X7)
% 0.46/0.67          | ~ (v1_funct_1 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.46/0.67               (k1_relset_1 @ sk_C @ sk_A_1 @ sk_E))
% 0.46/0.67          | ((k8_funct_2 @ X1 @ sk_C @ sk_A_1 @ X0 @ sk_E)
% 0.46/0.67              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A_1 @ X0 @ sk_E))
% 0.46/0.67          | ~ (v1_funct_1 @ sk_E))),
% 0.46/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.46/0.67          | ((sk_C) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.46/0.67               (k1_relset_1 @ sk_C @ sk_A_1 @ sk_E))
% 0.46/0.67          | ((k8_funct_2 @ X1 @ sk_C @ sk_A_1 @ X0 @ sk_E)
% 0.46/0.67              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A_1 @ X0 @ sk_E)))),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A_1 @ sk_D @ sk_E)
% 0.46/0.67          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A_1 @ sk_D @ sk_E))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0))
% 0.46/0.67        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.46/0.67        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '29'])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k1_partfun1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.67         ( v1_funct_1 @ F ) & 
% 0.46/0.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.67       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.67          | ~ (v1_funct_1 @ X11)
% 0.46/0.67          | ~ (v1_funct_1 @ X14)
% 0.46/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.67          | ((k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14)
% 0.46/0.67              = (k5_relat_1 @ X11 @ X14)))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.46/0.67            = (k5_relat_1 @ sk_D @ X0))
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.67  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.46/0.67            = (k5_relat_1 @ sk_D @ X0))
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.67          | ~ (v1_funct_1 @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ sk_E)
% 0.46/0.67        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A_1 @ sk_D @ sk_E)
% 0.46/0.67            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '36'])).
% 0.46/0.67  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A_1 @ sk_D @ sk_E)
% 0.46/0.67         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.46/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A_1 @ sk_D @ sk_E)
% 0.46/0.67          = (k5_relat_1 @ sk_D @ sk_E))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '39', '40', '41', '42'])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A_1 @ sk_D @ sk_E) @ sk_F)
% 0.46/0.67         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.46/0.67          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.46/0.67          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0))
% 0.46/0.67        | ~ (v1_funct_1 @ sk_E)
% 0.46/0.67        | ~ (v1_relat_1 @ sk_E)
% 0.46/0.67        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['23', '45'])).
% 0.46/0.67  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( v1_relat_1 @ C ) ))).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.67         ((v1_relat_1 @ X3)
% 0.46/0.67          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.67  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.67  thf('51', plain,
% 0.46/0.67      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.46/0.67          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0))
% 0.46/0.67        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['46', '47', '50'])).
% 0.46/0.67  thf('52', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.67  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.67  thf('54', plain, ($false),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '52', '53'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
