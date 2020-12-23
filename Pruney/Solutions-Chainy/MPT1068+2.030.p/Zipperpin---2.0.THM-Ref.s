%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XpYgm9UzAV

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:01 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 120 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  796 (2634 expanded)
%              Number of equality atoms :   46 ( 118 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['3','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k8_funct_2 @ X11 @ X9 @ X10 @ X12 @ X8 )
        = ( k1_partfun1 @ X11 @ X9 @ X9 @ X10 @ X12 @ X8 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X11 @ X9 @ X12 ) @ ( k1_relset_1 @ X9 @ X10 @ X8 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X9 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k1_partfun1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16 )
        = ( k5_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','33','34','35','36'])).

thf('38',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','46'])).

thf('48',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XpYgm9UzAV
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 210 iterations in 0.193s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.44/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.65  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.44/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(t185_funct_2, conjecture,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.44/0.65       ( ![D:$i]:
% 0.44/0.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.44/0.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.44/0.65           ( ![E:$i]:
% 0.44/0.65             ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.65                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.44/0.65               ( ![F:$i]:
% 0.44/0.65                 ( ( m1_subset_1 @ F @ B ) =>
% 0.44/0.65                   ( ( r1_tarski @
% 0.44/0.65                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.44/0.65                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.44/0.65                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.44/0.65                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.65        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.44/0.65          ( ![D:$i]:
% 0.44/0.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.44/0.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.44/0.65              ( ![E:$i]:
% 0.44/0.65                ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.65                    ( m1_subset_1 @
% 0.44/0.65                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.44/0.65                  ( ![F:$i]:
% 0.44/0.65                    ( ( m1_subset_1 @ F @ B ) =>
% 0.44/0.65                      ( ( r1_tarski @
% 0.44/0.65                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.44/0.65                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.44/0.65                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65                          ( ( k1_funct_1 @
% 0.44/0.65                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.44/0.65                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.44/0.65  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t2_subset, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ A @ B ) =>
% 0.44/0.65       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X2 : $i, X3 : $i]:
% 0.44/0.65         ((r2_hidden @ X2 @ X3)
% 0.44/0.65          | (v1_xboole_0 @ X3)
% 0.44/0.65          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [t2_subset])).
% 0.44/0.65  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.65  thf(t8_boole, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t8_boole])).
% 0.44/0.65  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((X0) != (k1_xboole_0))
% 0.44/0.65          | ~ (v1_xboole_0 @ sk_B)
% 0.44/0.65          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.65  thf('7', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.44/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.65  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.65  thf('9', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('simplify_reflect+', [status(thm)], ['7', '8'])).
% 0.44/0.65  thf('10', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.44/0.65      inference('clc', [status(thm)], ['3', '9'])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t21_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ![E:$i]:
% 0.44/0.65         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.44/0.65           ( ( r2_hidden @ C @ A ) =>
% 0.44/0.65             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.44/0.65                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X19)
% 0.44/0.65          | ~ (v1_funct_1 @ X19)
% 0.44/0.65          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.44/0.65              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 0.44/0.65          | ((X22) = (k1_xboole_0))
% 0.44/0.65          | ~ (r2_hidden @ X21 @ X23)
% 0.44/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.44/0.65          | ~ (v1_funct_2 @ X20 @ X23 @ X22)
% 0.44/0.65          | ~ (v1_funct_1 @ X20))),
% 0.44/0.65      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ sk_D)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.44/0.65          | ~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.65          | ((sk_C) = (k1_xboole_0))
% 0.44/0.65          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.44/0.65              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.44/0.65          | ~ (v1_funct_1 @ X1)
% 0.44/0.65          | ~ (v1_relat_1 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.65  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.65          | ((sk_C) = (k1_xboole_0))
% 0.44/0.65          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.44/0.65              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.44/0.65          | ~ (v1_funct_1 @ X1)
% 0.44/0.65          | ~ (v1_relat_1 @ X1))),
% 0.44/0.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.44/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.44/0.65          | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.44/0.65        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(d12_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ![E:$i]:
% 0.44/0.65         ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.65             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.44/0.65           ( ( r1_tarski @
% 0.44/0.65               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.44/0.65             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.44/0.65                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X8)
% 0.44/0.65          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.44/0.65          | ((k8_funct_2 @ X11 @ X9 @ X10 @ X12 @ X8)
% 0.44/0.65              = (k1_partfun1 @ X11 @ X9 @ X9 @ X10 @ X12 @ X8))
% 0.44/0.65          | ~ (r1_tarski @ (k2_relset_1 @ X11 @ X9 @ X12) @ 
% 0.44/0.65               (k1_relset_1 @ X9 @ X10 @ X8))
% 0.44/0.65          | ((X9) = (k1_xboole_0))
% 0.44/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.44/0.65          | ~ (v1_funct_2 @ X12 @ X11 @ X9)
% 0.44/0.65          | ~ (v1_funct_1 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X0)
% 0.44/0.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.44/0.65          | ((sk_C) = (k1_xboole_0))
% 0.44/0.65          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.44/0.65               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.44/0.65          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.44/0.65              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.65  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X0)
% 0.44/0.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.44/0.65          | ((sk_C) = (k1_xboole_0))
% 0.44/0.65          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.44/0.65               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.44/0.65          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.44/0.65              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 0.44/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.44/0.65          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 0.44/0.65        | ((sk_C) = (k1_xboole_0))
% 0.44/0.65        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.44/0.65        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '23'])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k1_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.65         ( v1_funct_1 @ F ) & 
% 0.44/0.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.44/0.65       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.44/0.65          | ~ (v1_funct_1 @ X13)
% 0.44/0.65          | ~ (v1_funct_1 @ X16)
% 0.44/0.65          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.44/0.65          | ((k1_partfun1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16)
% 0.44/0.65              = (k5_relat_1 @ X13 @ X16)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.44/0.65            = (k5_relat_1 @ sk_D @ X0))
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.65  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.44/0.65            = (k5_relat_1 @ sk_D @ X0))
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.44/0.65          | ~ (v1_funct_1 @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.44/0.65            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['25', '30'])).
% 0.44/0.65  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.44/0.65         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.44/0.65      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('37', plain,
% 0.44/0.65      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.44/0.65          = (k5_relat_1 @ sk_D @ sk_E))
% 0.44/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['24', '33', '34', '35', '36'])).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.44/0.65         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.44/0.65          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.44/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.44/0.65          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.44/0.65        | ((sk_C) = (k1_xboole_0))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ~ (v1_relat_1 @ sk_E)
% 0.44/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['17', '39'])).
% 0.44/0.65  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc2_relat_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ A ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X4 : $i, X5 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.44/0.65          | (v1_relat_1 @ X4)
% 0.44/0.65          | ~ (v1_relat_1 @ X5))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.44/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf(fc6_relat_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.65  thf('46', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.65      inference('demod', [status(thm)], ['44', '45'])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.44/0.65          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.44/0.65        | ((sk_C) = (k1_xboole_0))
% 0.44/0.65        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['40', '41', '46'])).
% 0.44/0.65  thf('48', plain, (((sk_C) = (k1_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.65  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.65  thf('50', plain, ($false),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '48', '49'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
