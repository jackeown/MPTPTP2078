%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjSkOChwfb

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:31 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 236 expanded)
%              Number of leaves         :   45 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          : 1496 (5538 expanded)
%              Number of equality atoms :   51 ( 132 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t193_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                 => ! [F: $i] :
                      ( ( m1_subset_1 @ F @ B )
                     => ( ( v1_partfun1 @ E @ A )
                       => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                          = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                   => ! [F: $i] :
                        ( ( m1_subset_1 @ F @ B )
                       => ( ( v1_partfun1 @ E @ A )
                         => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                            = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t193_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t131_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X33 )
      | ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t131_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( v1_partfun1 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('18',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t186_funct_2,axiom,(
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

thf('27',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X36 @ X37 @ X39 @ X35 @ X40 ) @ X38 )
        = ( k7_partfun1 @ X39 @ X40 @ ( k1_funct_1 @ X35 @ X38 ) ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X36 @ X37 @ X35 ) @ ( k1_relset_1 @ X37 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t186_funct_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k7_partfun1 @ X1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k7_partfun1 @ X1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','46','47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('54',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ( ( k3_funct_2 @ X29 @ X30 @ X28 @ X31 )
        = ( k1_funct_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['51','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C )
        & ( m1_subset_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X24 @ X25 @ X27 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ( ( k3_funct_2 @ X29 @ X30 @ X28 @ X31 )
        = ( k1_funct_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X24 @ X25 @ X27 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X24 @ X25 @ X27 @ X23 @ X26 ) @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','85','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['63','98'])).

thf('100',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['62','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['50','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjSkOChwfb
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:07:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 367 iterations in 0.306s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.76  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.76  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.76  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.58/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.76  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.58/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.76  thf(sk_F_type, type, sk_F: $i).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.76  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.76  thf(t193_funct_2, conjecture,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.58/0.76           ( ![C:$i,D:$i]:
% 0.58/0.76             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.58/0.76                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.58/0.76               ( ![E:$i]:
% 0.58/0.76                 ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.76                     ( m1_subset_1 @
% 0.58/0.76                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.58/0.76                   ( ![F:$i]:
% 0.58/0.76                     ( ( m1_subset_1 @ F @ B ) =>
% 0.58/0.76                       ( ( v1_partfun1 @ E @ A ) =>
% 0.58/0.76                         ( ( k3_funct_2 @
% 0.58/0.76                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.58/0.76                           ( k7_partfun1 @
% 0.58/0.76                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i]:
% 0.58/0.76        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.76          ( ![B:$i]:
% 0.58/0.76            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.58/0.76              ( ![C:$i,D:$i]:
% 0.58/0.76                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.58/0.76                    ( m1_subset_1 @
% 0.58/0.76                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.58/0.76                  ( ![E:$i]:
% 0.58/0.76                    ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.76                        ( m1_subset_1 @
% 0.58/0.76                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.58/0.76                      ( ![F:$i]:
% 0.58/0.76                        ( ( m1_subset_1 @ F @ B ) =>
% 0.58/0.76                          ( ( v1_partfun1 @ E @ A ) =>
% 0.58/0.76                            ( ( k3_funct_2 @
% 0.58/0.76                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.58/0.76                              ( k7_partfun1 @
% 0.58/0.76                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.58/0.76  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t131_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.76       ( ( v1_partfun1 @ C @ A ) =>
% 0.58/0.76         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.76           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.58/0.76         (~ (v1_partfun1 @ X32 @ X33)
% 0.58/0.76          | (v1_funct_2 @ X32 @ X33 @ X34)
% 0.58/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.58/0.76          | ~ (v1_funct_1 @ X32))),
% 0.58/0.76      inference('cnf', [status(esa)], [t131_funct_2])).
% 0.58/0.76  thf('4', plain,
% 0.58/0.76      ((~ (v1_funct_1 @ sk_E)
% 0.58/0.76        | (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.58/0.76        | ~ (v1_partfun1 @ sk_E @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.76  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('6', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.58/0.76      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.58/0.76  thf(d1_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_1, axiom,
% 0.58/0.76    (![C:$i,B:$i,A:$i]:
% 0.58/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.58/0.76          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.58/0.76          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_A)
% 0.58/0.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_C @ sk_E)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_4, axiom,
% 0.58/0.76    (![B:$i,A:$i]:
% 0.58/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.76  thf(zf_stmt_5, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.76         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.58/0.76          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.58/0.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.76  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc2_partfun1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.58/0.76       ( ![C:$i]:
% 0.58/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X12)
% 0.58/0.76          | ~ (v1_xboole_0 @ X13)
% 0.58/0.76          | ~ (v1_partfun1 @ X14 @ X12)
% 0.58/0.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.58/0.76        | ~ (v1_xboole_0 @ sk_C)
% 0.58/0.76        | (v1_xboole_0 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.76  thf('19', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('20', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['18', '19'])).
% 0.58/0.76  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('22', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.58/0.76      inference('clc', [status(thm)], ['20', '21'])).
% 0.58/0.76  thf('23', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.58/0.76      inference('sup-', [status(thm)], ['15', '22'])).
% 0.58/0.76  thf('24', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_A)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '23'])).
% 0.58/0.76  thf('25', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_C @ sk_E))),
% 0.58/0.76      inference('demod', [status(thm)], ['9', '24'])).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t186_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.58/0.76       ( ![D:$i]:
% 0.58/0.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.58/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.76           ( ![E:$i]:
% 0.58/0.76             ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.76                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.58/0.76               ( ![F:$i]:
% 0.58/0.76                 ( ( m1_subset_1 @ F @ B ) =>
% 0.58/0.76                   ( ( r1_tarski @
% 0.58/0.76                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.58/0.76                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.58/0.76                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.76                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.58/0.76                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.58/0.76         (~ (v1_funct_1 @ X35)
% 0.58/0.76          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.58/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.58/0.76          | ~ (m1_subset_1 @ X38 @ X36)
% 0.58/0.76          | ((k1_funct_1 @ (k8_funct_2 @ X36 @ X37 @ X39 @ X35 @ X40) @ X38)
% 0.58/0.76              = (k7_partfun1 @ X39 @ X40 @ (k1_funct_1 @ X35 @ X38)))
% 0.58/0.76          | ((X36) = (k1_xboole_0))
% 0.58/0.76          | ~ (r1_tarski @ (k2_relset_1 @ X36 @ X37 @ X35) @ 
% 0.58/0.76               (k1_relset_1 @ X37 @ X39 @ X40))
% 0.58/0.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X39)))
% 0.58/0.76          | ~ (v1_funct_1 @ X40)
% 0.58/0.76          | (v1_xboole_0 @ X37))),
% 0.58/0.76      inference('cnf', [status(esa)], [t186_funct_2])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ sk_A)
% 0.58/0.76          | ~ (v1_funct_1 @ X0)
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.58/0.76          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.58/0.76               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.58/0.76          | ((sk_B) = (k1_xboole_0))
% 0.58/0.76          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.58/0.76              = (k7_partfun1 @ X1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.58/0.76          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.58/0.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.58/0.76          | ~ (v1_funct_1 @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.76  thf('30', plain,
% 0.58/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.76         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.58/0.76          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.76  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ sk_A)
% 0.58/0.76          | ~ (v1_funct_1 @ X0)
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.58/0.76          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.58/0.76          | ((sk_B) = (k1_xboole_0))
% 0.58/0.76          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.58/0.76              = (k7_partfun1 @ X1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.58/0.76          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '31', '32', '33'])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.58/0.76              = (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.58/0.76          | ((sk_B) = (k1_xboole_0))
% 0.58/0.76          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.58/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.58/0.76          | (v1_xboole_0 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['25', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc2_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.76         ((v5_relat_1 @ X6 @ X8)
% 0.58/0.76          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.76  thf('38', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.58/0.76      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.76  thf(d19_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ B ) =>
% 0.58/0.76       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]:
% 0.58/0.76         (~ (v5_relat_1 @ X2 @ X3)
% 0.58/0.76          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.58/0.76          | ~ (v1_relat_1 @ X2))),
% 0.58/0.76      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc2_relat_1, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ A ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.58/0.76          | (v1_relat_1 @ X0)
% 0.58/0.76          | ~ (v1_relat_1 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.76  thf('43', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.76  thf(fc6_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.76  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.76  thf('46', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.58/0.76      inference('demod', [status(thm)], ['40', '45'])).
% 0.58/0.76  thf('47', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.58/0.76              = (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.58/0.76          | ((sk_B) = (k1_xboole_0))
% 0.58/0.76          | (v1_xboole_0 @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['35', '46', '47', '48'])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      (((v1_xboole_0 @ sk_A)
% 0.58/0.76        | ((sk_B) = (k1_xboole_0))
% 0.58/0.76        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.58/0.76            = (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '49'])).
% 0.58/0.76  thf('51', plain,
% 0.58/0.76      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.58/0.76         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.58/0.76         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.58/0.76             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('52', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k3_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.58/0.76         ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.76         ( m1_subset_1 @ D @ A ) ) =>
% 0.58/0.76       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.58/0.76  thf('54', plain,
% 0.58/0.76      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.58/0.76          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.58/0.76          | ~ (v1_funct_1 @ X28)
% 0.58/0.76          | (v1_xboole_0 @ X29)
% 0.58/0.76          | ~ (m1_subset_1 @ X31 @ X29)
% 0.58/0.76          | ((k3_funct_2 @ X29 @ X30 @ X28 @ X31) = (k1_funct_1 @ X28 @ X31)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.58/0.76  thf('55', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | (v1_xboole_0 @ sk_B)
% 0.58/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.76  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('58', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | (v1_xboole_0 @ sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.58/0.76  thf('59', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.58/0.76      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.58/0.76      inference('sup-', [status(thm)], ['52', '60'])).
% 0.58/0.76  thf('62', plain,
% 0.58/0.76      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.58/0.76         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.58/0.76         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.58/0.76      inference('demod', [status(thm)], ['51', '61'])).
% 0.58/0.76  thf('63', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('64', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('65', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(dt_k8_funct_2, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.76         ( v1_funct_1 @ E ) & 
% 0.58/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.76       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.58/0.76         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.58/0.76         ( m1_subset_1 @
% 0.58/0.76           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.58/0.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.76          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.58/0.76          | ~ (v1_funct_1 @ X23)
% 0.58/0.76          | ~ (v1_funct_1 @ X26)
% 0.58/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.58/0.76          | (m1_subset_1 @ (k8_funct_2 @ X24 @ X25 @ X27 @ X23 @ X26) @ 
% 0.58/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X27))))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.58/0.76  thf('67', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.58/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.58/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.76          | ~ (v1_funct_1 @ X1)
% 0.58/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.76  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('70', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.58/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.58/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.76          | ~ (v1_funct_1 @ X1))),
% 0.58/0.76      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.58/0.76  thf('71', plain,
% 0.58/0.76      ((~ (v1_funct_1 @ sk_E)
% 0.58/0.76        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.58/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['64', '70'])).
% 0.58/0.76  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('73', plain,
% 0.58/0.76      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.58/0.76      inference('demod', [status(thm)], ['71', '72'])).
% 0.58/0.76  thf('74', plain,
% 0.58/0.76      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.58/0.76          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.58/0.76          | ~ (v1_funct_1 @ X28)
% 0.58/0.76          | (v1_xboole_0 @ X29)
% 0.58/0.76          | ~ (m1_subset_1 @ X31 @ X29)
% 0.58/0.76          | ((k3_funct_2 @ X29 @ X30 @ X28 @ X31) = (k1_funct_1 @ X28 @ X31)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.58/0.76  thf('75', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.58/0.76            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.58/0.76            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.58/0.76               X0))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | (v1_xboole_0 @ sk_B)
% 0.58/0.76          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.58/0.76          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.58/0.76               sk_B @ sk_C))),
% 0.58/0.76      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.76  thf('76', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('77', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('78', plain,
% 0.58/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.76          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.58/0.76          | ~ (v1_funct_1 @ X23)
% 0.58/0.76          | ~ (v1_funct_1 @ X26)
% 0.58/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.58/0.76          | (v1_funct_1 @ (k8_funct_2 @ X24 @ X25 @ X27 @ X23 @ X26)))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.58/0.76  thf('79', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.58/0.76          | ~ (v1_funct_1 @ X0)
% 0.58/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['77', '78'])).
% 0.58/0.76  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('81', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('82', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.58/0.76          | ~ (v1_funct_1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.58/0.76  thf('83', plain,
% 0.58/0.76      ((~ (v1_funct_1 @ sk_E)
% 0.58/0.76        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['76', '82'])).
% 0.58/0.76  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('85', plain,
% 0.58/0.76      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.58/0.76      inference('demod', [status(thm)], ['83', '84'])).
% 0.58/0.76  thf('86', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('87', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('88', plain,
% 0.58/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.76          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.58/0.76          | ~ (v1_funct_1 @ X23)
% 0.58/0.76          | ~ (v1_funct_1 @ X26)
% 0.58/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.58/0.76          | (v1_funct_2 @ (k8_funct_2 @ X24 @ X25 @ X27 @ X23 @ X26) @ X24 @ 
% 0.58/0.76             X27))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.58/0.76  thf('89', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.58/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.76          | ~ (v1_funct_1 @ X1)
% 0.58/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['87', '88'])).
% 0.58/0.76  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('91', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('92', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.58/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.58/0.76          | ~ (v1_funct_1 @ X1))),
% 0.58/0.76      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.58/0.76  thf('93', plain,
% 0.58/0.76      ((~ (v1_funct_1 @ sk_E)
% 0.58/0.76        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.58/0.76           sk_B @ sk_C))),
% 0.58/0.76      inference('sup-', [status(thm)], ['86', '92'])).
% 0.58/0.76  thf('94', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('95', plain,
% 0.58/0.76      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.58/0.76        sk_C)),
% 0.58/0.76      inference('demod', [status(thm)], ['93', '94'])).
% 0.58/0.76  thf('96', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.58/0.76            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.58/0.76            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.58/0.76               X0))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | (v1_xboole_0 @ sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['75', '85', '95'])).
% 0.58/0.76  thf('97', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('98', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.76          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.58/0.76              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.58/0.76              = (k1_funct_1 @ 
% 0.58/0.76                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.58/0.76      inference('clc', [status(thm)], ['96', '97'])).
% 0.58/0.76  thf('99', plain,
% 0.58/0.76      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.58/0.76         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.58/0.76         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.58/0.76      inference('sup-', [status(thm)], ['63', '98'])).
% 0.58/0.76  thf('100', plain,
% 0.58/0.76      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.58/0.76         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.58/0.76      inference('demod', [status(thm)], ['62', '99'])).
% 0.58/0.76  thf('101', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.76      inference('simplify_reflect-', [status(thm)], ['50', '100'])).
% 0.58/0.76  thf('102', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('103', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.76      inference('clc', [status(thm)], ['101', '102'])).
% 0.58/0.76  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.76  thf('105', plain, ($false),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '103', '104'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
