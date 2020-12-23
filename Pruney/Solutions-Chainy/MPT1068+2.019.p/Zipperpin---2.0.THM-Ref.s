%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.emgidlpTv2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:59 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 133 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  823 (2699 expanded)
%              Number of equality atoms :   48 ( 121 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k1_funct_1 @ X23 @ ( k1_funct_1 @ X24 @ X25 ) ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
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
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
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
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
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

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
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
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 )
        = ( k5_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0 )
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
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','39','40','41','42'])).

thf('44',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    inference('sup-',[status(thm)],['10','13'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.emgidlpTv2
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 172 iterations in 0.104s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(t185_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.38/0.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.38/0.56           ( ![E:$i]:
% 0.38/0.56             ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.38/0.56               ( ![F:$i]:
% 0.38/0.56                 ( ( m1_subset_1 @ F @ B ) =>
% 0.38/0.56                   ( ( r1_tarski @
% 0.38/0.56                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.38/0.56                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.38/0.56                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.38/0.56                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.38/0.56          ( ![D:$i]:
% 0.38/0.56            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.38/0.56                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.38/0.56              ( ![E:$i]:
% 0.38/0.56                ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56                    ( m1_subset_1 @
% 0.38/0.56                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.38/0.56                  ( ![F:$i]:
% 0.38/0.56                    ( ( m1_subset_1 @ F @ B ) =>
% 0.38/0.56                      ( ( r1_tarski @
% 0.38/0.56                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.38/0.56                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.38/0.56                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56                          ( ( k1_funct_1 @
% 0.38/0.56                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.38/0.56                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.38/0.56  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t2_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X5 : $i, X6 : $i]:
% 0.38/0.56         ((r2_hidden @ X5 @ X6)
% 0.38/0.56          | (v1_xboole_0 @ X6)
% 0.38/0.56          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.56  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf(l13_xboole_0, axiom,
% 0.38/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((X0) != (k1_xboole_0))
% 0.38/0.56          | ~ (v1_xboole_0 @ X0)
% 0.38/0.56          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf('9', plain, ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.56  thf('10', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf(t7_ordinal1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '13'])).
% 0.38/0.56  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('simplify_reflect+', [status(thm)], ['9', '14'])).
% 0.38/0.56  thf('16', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 0.38/0.56      inference('clc', [status(thm)], ['3', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t21_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.56       ( ![E:$i]:
% 0.38/0.56         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.38/0.56           ( ( r2_hidden @ C @ A ) =>
% 0.38/0.56             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.38/0.56                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X23)
% 0.38/0.56          | ~ (v1_funct_1 @ X23)
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.38/0.56              = (k1_funct_1 @ X23 @ (k1_funct_1 @ X24 @ X25)))
% 0.38/0.56          | ((X26) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X25 @ X27)
% 0.38/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.38/0.56          | ~ (v1_funct_2 @ X24 @ X27 @ X26)
% 0.38/0.56          | ~ (v1_funct_1 @ X24))),
% 0.38/0.56      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_funct_1 @ sk_D)
% 0.38/0.56          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.38/0.56          | ((sk_C) = (k1_xboole_0))
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.38/0.56              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.38/0.56          | ((sk_C) = (k1_xboole_0))
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.38/0.56              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.38/0.56          | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.38/0.56        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d12_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.56       ( ![E:$i]:
% 0.38/0.56         ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.38/0.56           ( ( r1_tarski @
% 0.38/0.56               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.38/0.56             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.38/0.56                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.56         (~ (v1_funct_1 @ X12)
% 0.38/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.56          | ((k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12)
% 0.38/0.56              = (k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12))
% 0.38/0.56          | ~ (r1_tarski @ (k2_relset_1 @ X15 @ X13 @ X16) @ 
% 0.38/0.56               (k1_relset_1 @ X13 @ X14 @ X12))
% 0.38/0.56          | ((X13) = (k1_xboole_0))
% 0.38/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 0.38/0.56          | ~ (v1_funct_2 @ X16 @ X15 @ X13)
% 0.38/0.56          | ~ (v1_funct_1 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.38/0.56          | ((sk_C) = (k1_xboole_0))
% 0.38/0.56          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.38/0.56               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.38/0.56          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.38/0.56              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 0.38/0.56          | ~ (v1_funct_1 @ sk_E))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.38/0.56          | ((sk_C) = (k1_xboole_0))
% 0.38/0.56          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.38/0.56               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.38/0.56          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.38/0.56              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 0.38/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      ((((k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.38/0.56          = (k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0))
% 0.38/0.56        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))
% 0.38/0.56        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_partfun1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.56         ( v1_funct_1 @ F ) & 
% 0.38/0.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | ~ (v1_funct_1 @ X20)
% 0.38/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.56          | ((k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20)
% 0.38/0.56              = (k5_relat_1 @ X17 @ X20)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.38/0.56            = (k5_relat_1 @ sk_D @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.38/0.56            = (k5_relat_1 @ sk_D @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_E)
% 0.38/0.56        | ((k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.38/0.56            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '36'])).
% 0.38/0.56  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (((k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.38/0.56         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.38/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      ((((k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.38/0.56          = (k5_relat_1 @ sk_D @ sk_E))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['30', '39', '40', '41', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.38/0.56         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.38/0.56          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.38/0.56          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0))
% 0.38/0.56        | ~ (v1_funct_1 @ sk_E)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_E)
% 0.38/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '45'])).
% 0.38/0.56  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( v1_relat_1 @ C ) ))).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         ((v1_relat_1 @ X9)
% 0.38/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.56  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.38/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.38/0.56          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['46', '47', '50'])).
% 0.38/0.56  thf('52', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.38/0.56  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '13'])).
% 0.38/0.56  thf('54', plain, ($false),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '52', '53'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
