%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XoI7ebyRQT

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 130 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  838 (2703 expanded)
%              Number of equality atoms :   48 ( 120 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference(clc,[status(thm)],['3','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k1_funct_1 @ X26 @ ( k1_funct_1 @ X27 @ X28 ) ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
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
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_funct_2 @ X18 @ X16 @ X17 @ X19 @ X15 )
        = ( k1_partfun1 @ X18 @ X16 @ X16 @ X17 @ X19 @ X15 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X18 @ X16 @ X19 ) @ ( k1_relset_1 @ X16 @ X17 @ X15 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X16 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
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
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','39','40','41','42'])).

thf('44',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','50'])).

thf('52',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XoI7ebyRQT
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:59:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 306 iterations in 0.212s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.66  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.45/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.66  thf(t185_funct_2, conjecture,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.45/0.66       ( ![D:$i]:
% 0.45/0.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.66           ( ![E:$i]:
% 0.45/0.66             ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.45/0.66               ( ![F:$i]:
% 0.45/0.66                 ( ( m1_subset_1 @ F @ B ) =>
% 0.45/0.66                   ( ( r1_tarski @
% 0.45/0.66                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.45/0.66                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.45/0.66                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.45/0.66                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.66        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.45/0.66          ( ![D:$i]:
% 0.45/0.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.66              ( ![E:$i]:
% 0.45/0.66                ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66                    ( m1_subset_1 @
% 0.45/0.66                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.45/0.66                  ( ![F:$i]:
% 0.45/0.66                    ( ( m1_subset_1 @ F @ B ) =>
% 0.45/0.66                      ( ( r1_tarski @
% 0.45/0.66                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.45/0.66                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.45/0.66                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66                          ( ( k1_funct_1 @
% 0.45/0.66                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.45/0.66                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.45/0.66  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t2_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.66       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((r2_hidden @ X10 @ X11)
% 0.45/0.66          | (v1_xboole_0 @ X11)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.66  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf(d3_tarski, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X4 : $i, X6 : $i]:
% 0.45/0.66         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.66  thf(d1_xboole_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X7 : $i, X9 : $i]:
% 0.45/0.66         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '9'])).
% 0.45/0.66  thf('11', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) != (k1_xboole_0))
% 0.45/0.66          | ~ (v1_xboole_0 @ sk_B_1)
% 0.45/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.66  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.66  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.45/0.66      inference('simplify_reflect+', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf('16', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 0.45/0.66      inference('clc', [status(thm)], ['3', '15'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t21_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ![E:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.45/0.66           ( ( r2_hidden @ C @ A ) =>
% 0.45/0.66             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.45/0.66                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X26)
% 0.45/0.66          | ~ (v1_funct_1 @ X26)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ X27 @ X26) @ X28)
% 0.45/0.66              = (k1_funct_1 @ X26 @ (k1_funct_1 @ X27 @ X28)))
% 0.45/0.66          | ((X29) = (k1_xboole_0))
% 0.45/0.66          | ~ (r2_hidden @ X28 @ X30)
% 0.45/0.66          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.45/0.66          | ~ (v1_funct_2 @ X27 @ X30 @ X29)
% 0.45/0.66          | ~ (v1_funct_1 @ X27))),
% 0.45/0.66      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ sk_D)
% 0.45/0.66          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.45/0.66          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.45/0.66          | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.45/0.66              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.66  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.45/0.66          | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.45/0.66              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.45/0.66              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.45/0.66          | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.45/0.66        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d12_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ![E:$i]:
% 0.45/0.66         ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.66           ( ( r1_tarski @
% 0.45/0.66               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.45/0.66             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.45/0.66                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X15)
% 0.45/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.45/0.66          | ((k8_funct_2 @ X18 @ X16 @ X17 @ X19 @ X15)
% 0.45/0.66              = (k1_partfun1 @ X18 @ X16 @ X16 @ X17 @ X19 @ X15))
% 0.45/0.66          | ~ (r1_tarski @ (k2_relset_1 @ X18 @ X16 @ X19) @ 
% 0.45/0.66               (k1_relset_1 @ X16 @ X17 @ X15))
% 0.45/0.66          | ((X16) = (k1_xboole_0))
% 0.45/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.45/0.66          | ~ (v1_funct_2 @ X19 @ X18 @ X16)
% 0.45/0.66          | ~ (v1_funct_1 @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.45/0.66          | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 0.45/0.66               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.45/0.66          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 0.45/0.66              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E))
% 0.45/0.66          | ~ (v1_funct_1 @ sk_E))),
% 0.45/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.66  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.45/0.66          | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 0.45/0.66               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.45/0.66          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 0.45/0.66              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E)))),
% 0.45/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.45/0.66          = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66        | ~ (m1_subset_1 @ sk_D @ 
% 0.45/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))
% 0.45/0.66        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['24', '29'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k1_partfun1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.66         ( v1_funct_1 @ F ) & 
% 0.45/0.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.66       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.66          | ~ (v1_funct_1 @ X20)
% 0.45/0.66          | ~ (v1_funct_1 @ X23)
% 0.45/0.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.45/0.66          | ((k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 0.45/0.66              = (k5_relat_1 @ X20 @ X23)))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 0.45/0.66            = (k5_relat_1 @ sk_D @ X0))
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 0.45/0.66            = (k5_relat_1 @ sk_D @ X0))
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.66          | ~ (v1_funct_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_E)
% 0.45/0.66        | ((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.45/0.66            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['31', '36'])).
% 0.45/0.66  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.45/0.66         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.45/0.66          = (k5_relat_1 @ sk_D @ sk_E))
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['30', '39', '40', '41', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.45/0.66         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.45/0.66          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.45/0.66          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_E)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_E)
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '45'])).
% 0.45/0.66  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc1_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( v1_relat_1 @ C ) ))).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.66         ((v1_relat_1 @ X12)
% 0.45/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.66  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.66      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.45/0.66          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['46', '47', '50'])).
% 0.45/0.66  thf('52', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.66  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.66  thf('54', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['0', '52', '53'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
