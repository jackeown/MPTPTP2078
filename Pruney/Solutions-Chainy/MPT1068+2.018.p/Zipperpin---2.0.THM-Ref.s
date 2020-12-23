%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NZq5LeFXnH

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:59 EST 2020

% Result     : Theorem 51.33s
% Output     : Refutation 51.33s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 198 expanded)
%              Number of leaves         :   44 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          : 1075 (3583 expanded)
%              Number of equality atoms :   66 ( 162 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['3','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['25','34'])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k1_funct_1 @ X13 @ ( k1_funct_1 @ X14 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['18','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_funct_2 @ X25 @ X23 @ X24 @ X26 @ X22 )
        = ( k1_partfun1 @ X25 @ X23 @ X23 @ X24 @ X26 @ X22 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X25 @ X23 @ X26 ) @ ( k1_relset_1 @ X23 @ X24 @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('62',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','68'])).

thf('70',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NZq5LeFXnH
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 51.33/51.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.33/51.55  % Solved by: fo/fo7.sh
% 51.33/51.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.33/51.55  % done 13056 iterations in 51.091s
% 51.33/51.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.33/51.55  % SZS output start Refutation
% 51.33/51.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 51.33/51.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.33/51.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 51.33/51.55  thf(sk_A_type, type, sk_A: $i).
% 51.33/51.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 51.33/51.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 51.33/51.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 51.33/51.55  thf(sk_D_type, type, sk_D: $i).
% 51.33/51.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 51.33/51.55  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 51.33/51.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 51.33/51.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.33/51.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 51.33/51.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 51.33/51.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 51.33/51.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 51.33/51.55  thf(sk_B_type, type, sk_B: $i).
% 51.33/51.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 51.33/51.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 51.33/51.55  thf(sk_E_type, type, sk_E: $i).
% 51.33/51.55  thf(sk_F_type, type, sk_F: $i).
% 51.33/51.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 51.33/51.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 51.33/51.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 51.33/51.55  thf(sk_C_type, type, sk_C: $i).
% 51.33/51.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 51.33/51.55  thf(t185_funct_2, conjecture,
% 51.33/51.55    (![A:$i,B:$i,C:$i]:
% 51.33/51.55     ( ( ~( v1_xboole_0 @ C ) ) =>
% 51.33/51.55       ( ![D:$i]:
% 51.33/51.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 51.33/51.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 51.33/51.55           ( ![E:$i]:
% 51.33/51.55             ( ( ( v1_funct_1 @ E ) & 
% 51.33/51.55                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 51.33/51.55               ( ![F:$i]:
% 51.33/51.55                 ( ( m1_subset_1 @ F @ B ) =>
% 51.33/51.55                   ( ( r1_tarski @
% 51.33/51.55                       ( k2_relset_1 @ B @ C @ D ) @ 
% 51.33/51.55                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 51.33/51.55                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 51.33/51.55                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 51.33/51.55                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 51.33/51.55  thf(zf_stmt_0, negated_conjecture,
% 51.33/51.55    (~( ![A:$i,B:$i,C:$i]:
% 51.33/51.55        ( ( ~( v1_xboole_0 @ C ) ) =>
% 51.33/51.55          ( ![D:$i]:
% 51.33/51.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 51.33/51.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 51.33/51.55              ( ![E:$i]:
% 51.33/51.55                ( ( ( v1_funct_1 @ E ) & 
% 51.33/51.55                    ( m1_subset_1 @
% 51.33/51.55                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 51.33/51.55                  ( ![F:$i]:
% 51.33/51.55                    ( ( m1_subset_1 @ F @ B ) =>
% 51.33/51.55                      ( ( r1_tarski @
% 51.33/51.55                          ( k2_relset_1 @ B @ C @ D ) @ 
% 51.33/51.55                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 51.33/51.55                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 51.33/51.55                          ( ( k1_funct_1 @
% 51.33/51.55                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 51.33/51.55                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 51.33/51.55    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 51.33/51.55  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(t2_subset, axiom,
% 51.33/51.55    (![A:$i,B:$i]:
% 51.33/51.55     ( ( m1_subset_1 @ A @ B ) =>
% 51.33/51.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 51.33/51.55  thf('2', plain,
% 51.33/51.55      (![X5 : $i, X6 : $i]:
% 51.33/51.55         ((r2_hidden @ X5 @ X6)
% 51.33/51.55          | (v1_xboole_0 @ X6)
% 51.33/51.55          | ~ (m1_subset_1 @ X5 @ X6))),
% 51.33/51.55      inference('cnf', [status(esa)], [t2_subset])).
% 51.33/51.55  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 51.33/51.55      inference('sup-', [status(thm)], ['1', '2'])).
% 51.33/51.55  thf(l13_xboole_0, axiom,
% 51.33/51.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 51.33/51.55  thf('4', plain,
% 51.33/51.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 51.33/51.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 51.33/51.55  thf('5', plain,
% 51.33/51.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 51.33/51.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 51.33/51.55  thf('6', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i]:
% 51.33/51.55         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 51.33/51.55      inference('sup+', [status(thm)], ['4', '5'])).
% 51.33/51.55  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('8', plain,
% 51.33/51.55      (![X0 : $i]:
% 51.33/51.55         (((X0) != (k1_xboole_0))
% 51.33/51.55          | ~ (v1_xboole_0 @ X0)
% 51.33/51.55          | ~ (v1_xboole_0 @ sk_B))),
% 51.33/51.55      inference('sup-', [status(thm)], ['6', '7'])).
% 51.33/51.55  thf('9', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 51.33/51.55      inference('simplify', [status(thm)], ['8'])).
% 51.33/51.55  thf(t4_subset_1, axiom,
% 51.33/51.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 51.33/51.55  thf('10', plain,
% 51.33/51.55      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 51.33/51.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 51.33/51.55  thf(t3_subset, axiom,
% 51.33/51.55    (![A:$i,B:$i]:
% 51.33/51.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.33/51.55  thf('11', plain,
% 51.33/51.55      (![X7 : $i, X8 : $i]:
% 51.33/51.55         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 51.33/51.55      inference('cnf', [status(esa)], [t3_subset])).
% 51.33/51.55  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 51.33/51.55      inference('sup-', [status(thm)], ['10', '11'])).
% 51.33/51.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 51.33/51.55  thf('13', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 51.33/51.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 51.33/51.55  thf(t69_xboole_1, axiom,
% 51.33/51.55    (![A:$i,B:$i]:
% 51.33/51.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 51.33/51.55       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 51.33/51.55  thf('14', plain,
% 51.33/51.55      (![X2 : $i, X3 : $i]:
% 51.33/51.55         (~ (r1_xboole_0 @ X2 @ X3)
% 51.33/51.55          | ~ (r1_tarski @ X2 @ X3)
% 51.33/51.55          | (v1_xboole_0 @ X2))),
% 51.33/51.55      inference('cnf', [status(esa)], [t69_xboole_1])).
% 51.33/51.55  thf('15', plain,
% 51.33/51.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 51.33/51.55      inference('sup-', [status(thm)], ['13', '14'])).
% 51.33/51.55  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 51.33/51.55      inference('sup-', [status(thm)], ['12', '15'])).
% 51.33/51.55  thf('17', plain, (~ (v1_xboole_0 @ sk_B)),
% 51.33/51.55      inference('demod', [status(thm)], ['9', '16'])).
% 51.33/51.55  thf('18', plain, ((r2_hidden @ sk_F @ sk_B)),
% 51.33/51.55      inference('clc', [status(thm)], ['3', '17'])).
% 51.33/51.55  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(d1_funct_2, axiom,
% 51.33/51.55    (![A:$i,B:$i,C:$i]:
% 51.33/51.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.33/51.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 51.33/51.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 51.33/51.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 51.33/51.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 51.33/51.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 51.33/51.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 51.33/51.55  thf(zf_stmt_1, axiom,
% 51.33/51.55    (![C:$i,B:$i,A:$i]:
% 51.33/51.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 51.33/51.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 51.33/51.55  thf('20', plain,
% 51.33/51.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 51.33/51.55         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 51.33/51.55          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 51.33/51.55          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 51.33/51.55  thf('21', plain,
% 51.33/51.55      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 51.33/51.55        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 51.33/51.55      inference('sup-', [status(thm)], ['19', '20'])).
% 51.33/51.55  thf('22', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(redefinition_k1_relset_1, axiom,
% 51.33/51.55    (![A:$i,B:$i,C:$i]:
% 51.33/51.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.33/51.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 51.33/51.55  thf('23', plain,
% 51.33/51.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.33/51.55         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 51.33/51.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 51.33/51.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 51.33/51.55  thf('24', plain,
% 51.33/51.55      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 51.33/51.55      inference('sup-', [status(thm)], ['22', '23'])).
% 51.33/51.55  thf('25', plain,
% 51.33/51.55      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 51.33/51.55      inference('demod', [status(thm)], ['21', '24'])).
% 51.33/51.55  thf('26', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 51.33/51.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 51.33/51.55  thf(zf_stmt_4, axiom,
% 51.33/51.55    (![B:$i,A:$i]:
% 51.33/51.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 51.33/51.55       ( zip_tseitin_0 @ B @ A ) ))).
% 51.33/51.55  thf(zf_stmt_5, axiom,
% 51.33/51.55    (![A:$i,B:$i,C:$i]:
% 51.33/51.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.33/51.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 51.33/51.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 51.33/51.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 51.33/51.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 51.33/51.55  thf('27', plain,
% 51.33/51.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 51.33/51.55         (~ (zip_tseitin_0 @ X32 @ X33)
% 51.33/51.55          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 51.33/51.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 51.33/51.55  thf('28', plain,
% 51.33/51.55      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 51.33/51.55      inference('sup-', [status(thm)], ['26', '27'])).
% 51.33/51.55  thf('29', plain,
% 51.33/51.55      (![X27 : $i, X28 : $i]:
% 51.33/51.55         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 51.33/51.55  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 51.33/51.55      inference('sup-', [status(thm)], ['12', '15'])).
% 51.33/51.55  thf('31', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 51.33/51.55      inference('sup+', [status(thm)], ['29', '30'])).
% 51.33/51.55  thf('32', plain, (~ (v1_xboole_0 @ sk_C)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('33', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 51.33/51.55      inference('sup-', [status(thm)], ['31', '32'])).
% 51.33/51.55  thf('34', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 51.33/51.55      inference('demod', [status(thm)], ['28', '33'])).
% 51.33/51.55  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 51.33/51.55      inference('demod', [status(thm)], ['25', '34'])).
% 51.33/51.55  thf(t23_funct_1, axiom,
% 51.33/51.55    (![A:$i,B:$i]:
% 51.33/51.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 51.33/51.55       ( ![C:$i]:
% 51.33/51.55         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 51.33/51.55           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 51.33/51.55             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 51.33/51.55               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 51.33/51.55  thf('36', plain,
% 51.33/51.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 51.33/51.55         (~ (v1_relat_1 @ X13)
% 51.33/51.55          | ~ (v1_funct_1 @ X13)
% 51.33/51.55          | ((k1_funct_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 51.33/51.55              = (k1_funct_1 @ X13 @ (k1_funct_1 @ X14 @ X15)))
% 51.33/51.55          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 51.33/51.55          | ~ (v1_funct_1 @ X14)
% 51.33/51.55          | ~ (v1_relat_1 @ X14))),
% 51.33/51.55      inference('cnf', [status(esa)], [t23_funct_1])).
% 51.33/51.55  thf('37', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i]:
% 51.33/51.55         (~ (r2_hidden @ X0 @ sk_B)
% 51.33/51.55          | ~ (v1_relat_1 @ sk_D)
% 51.33/51.55          | ~ (v1_funct_1 @ sk_D)
% 51.33/51.55          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 51.33/51.55              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 51.33/51.55          | ~ (v1_funct_1 @ X1)
% 51.33/51.55          | ~ (v1_relat_1 @ X1))),
% 51.33/51.55      inference('sup-', [status(thm)], ['35', '36'])).
% 51.33/51.55  thf('38', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(cc1_relset_1, axiom,
% 51.33/51.55    (![A:$i,B:$i,C:$i]:
% 51.33/51.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.33/51.55       ( v1_relat_1 @ C ) ))).
% 51.33/51.55  thf('39', plain,
% 51.33/51.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.33/51.55         ((v1_relat_1 @ X16)
% 51.33/51.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 51.33/51.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 51.33/51.55  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 51.33/51.55      inference('sup-', [status(thm)], ['38', '39'])).
% 51.33/51.55  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('42', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i]:
% 51.33/51.55         (~ (r2_hidden @ X0 @ sk_B)
% 51.33/51.55          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 51.33/51.55              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 51.33/51.55          | ~ (v1_funct_1 @ X1)
% 51.33/51.55          | ~ (v1_relat_1 @ X1))),
% 51.33/51.55      inference('demod', [status(thm)], ['37', '40', '41'])).
% 51.33/51.55  thf('43', plain,
% 51.33/51.55      (![X0 : $i]:
% 51.33/51.55         (~ (v1_relat_1 @ X0)
% 51.33/51.55          | ~ (v1_funct_1 @ X0)
% 51.33/51.55          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 51.33/51.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F))))),
% 51.33/51.55      inference('sup-', [status(thm)], ['18', '42'])).
% 51.33/51.55  thf('44', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('45', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(redefinition_k1_partfun1, axiom,
% 51.33/51.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 51.33/51.55     ( ( ( v1_funct_1 @ E ) & 
% 51.33/51.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 51.33/51.55         ( v1_funct_1 @ F ) & 
% 51.33/51.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 51.33/51.55       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 51.33/51.55  thf('46', plain,
% 51.33/51.55      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 51.33/51.55         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 51.33/51.55          | ~ (v1_funct_1 @ X35)
% 51.33/51.55          | ~ (v1_funct_1 @ X38)
% 51.33/51.55          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 51.33/51.55          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 51.33/51.55              = (k5_relat_1 @ X35 @ X38)))),
% 51.33/51.55      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 51.33/51.55  thf('47', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.33/51.55         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 51.33/51.55            = (k5_relat_1 @ sk_D @ X0))
% 51.33/51.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 51.33/51.55          | ~ (v1_funct_1 @ X0)
% 51.33/51.55          | ~ (v1_funct_1 @ sk_D))),
% 51.33/51.55      inference('sup-', [status(thm)], ['45', '46'])).
% 51.33/51.55  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('49', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.33/51.55         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 51.33/51.55            = (k5_relat_1 @ sk_D @ X0))
% 51.33/51.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 51.33/51.55          | ~ (v1_funct_1 @ X0))),
% 51.33/51.55      inference('demod', [status(thm)], ['47', '48'])).
% 51.33/51.55  thf('50', plain,
% 51.33/51.55      ((~ (v1_funct_1 @ sk_E)
% 51.33/51.55        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 51.33/51.55            = (k5_relat_1 @ sk_D @ sk_E)))),
% 51.33/51.55      inference('sup-', [status(thm)], ['44', '49'])).
% 51.33/51.55  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('52', plain,
% 51.33/51.55      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 51.33/51.55         = (k5_relat_1 @ sk_D @ sk_E))),
% 51.33/51.55      inference('demod', [status(thm)], ['50', '51'])).
% 51.33/51.55  thf('53', plain,
% 51.33/51.55      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 51.33/51.55        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('54', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('55', plain,
% 51.33/51.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.33/51.55         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 51.33/51.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 51.33/51.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 51.33/51.55  thf('56', plain,
% 51.33/51.55      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 51.33/51.55      inference('sup-', [status(thm)], ['54', '55'])).
% 51.33/51.55  thf('57', plain,
% 51.33/51.55      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 51.33/51.55      inference('demod', [status(thm)], ['53', '56'])).
% 51.33/51.55  thf('58', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf(d12_funct_2, axiom,
% 51.33/51.55    (![A:$i,B:$i,C:$i,D:$i]:
% 51.33/51.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 51.33/51.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 51.33/51.55       ( ![E:$i]:
% 51.33/51.55         ( ( ( v1_funct_1 @ E ) & 
% 51.33/51.55             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 51.33/51.55           ( ( r1_tarski @
% 51.33/51.55               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 51.33/51.55             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 51.33/51.55               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 51.33/51.55                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 51.33/51.55  thf('59', plain,
% 51.33/51.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 51.33/51.55         (~ (v1_funct_1 @ X22)
% 51.33/51.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 51.33/51.55          | ((k8_funct_2 @ X25 @ X23 @ X24 @ X26 @ X22)
% 51.33/51.55              = (k1_partfun1 @ X25 @ X23 @ X23 @ X24 @ X26 @ X22))
% 51.33/51.55          | ~ (r1_tarski @ (k2_relset_1 @ X25 @ X23 @ X26) @ 
% 51.33/51.55               (k1_relset_1 @ X23 @ X24 @ X22))
% 51.33/51.55          | ((X23) = (k1_xboole_0))
% 51.33/51.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 51.33/51.55          | ~ (v1_funct_2 @ X26 @ X25 @ X23)
% 51.33/51.55          | ~ (v1_funct_1 @ X26))),
% 51.33/51.55      inference('cnf', [status(esa)], [d12_funct_2])).
% 51.33/51.55  thf('60', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i]:
% 51.33/51.55         (~ (v1_funct_1 @ X0)
% 51.33/51.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 51.33/51.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 51.33/51.55          | ((sk_C) = (k1_xboole_0))
% 51.33/51.55          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 51.33/51.55               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 51.33/51.55          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 51.33/51.55              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 51.33/51.55          | ~ (v1_funct_1 @ sk_E))),
% 51.33/51.55      inference('sup-', [status(thm)], ['58', '59'])).
% 51.33/51.55  thf('61', plain,
% 51.33/51.55      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 51.33/51.55      inference('sup-', [status(thm)], ['54', '55'])).
% 51.33/51.55  thf('62', plain, ((v1_funct_1 @ sk_E)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('63', plain,
% 51.33/51.55      (![X0 : $i, X1 : $i]:
% 51.33/51.55         (~ (v1_funct_1 @ X0)
% 51.33/51.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 51.33/51.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 51.33/51.55          | ((sk_C) = (k1_xboole_0))
% 51.33/51.55          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 51.33/51.55          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 51.33/51.55              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 51.33/51.55      inference('demod', [status(thm)], ['60', '61', '62'])).
% 51.33/51.55  thf('64', plain,
% 51.33/51.55      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 51.33/51.55          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 51.33/51.55        | ((sk_C) = (k1_xboole_0))
% 51.33/51.55        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 51.33/51.55        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 51.33/51.55        | ~ (v1_funct_1 @ sk_D))),
% 51.33/51.55      inference('sup-', [status(thm)], ['57', '63'])).
% 51.33/51.55  thf('65', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('68', plain,
% 51.33/51.55      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 51.33/51.55          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 51.33/51.55        | ((sk_C) = (k1_xboole_0)))),
% 51.33/51.55      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 51.33/51.55  thf('69', plain,
% 51.33/51.55      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 51.33/51.55          = (k5_relat_1 @ sk_D @ sk_E))
% 51.33/51.55        | ((sk_C) = (k1_xboole_0)))),
% 51.33/51.55      inference('sup+', [status(thm)], ['52', '68'])).
% 51.33/51.55  thf('70', plain,
% 51.33/51.55      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 51.33/51.55         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('71', plain,
% 51.33/51.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 51.33/51.55          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 51.33/51.55        | ((sk_C) = (k1_xboole_0)))),
% 51.33/51.55      inference('sup-', [status(thm)], ['69', '70'])).
% 51.33/51.55  thf('72', plain,
% 51.33/51.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 51.33/51.55          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 51.33/51.55        | ~ (v1_funct_1 @ sk_E)
% 51.33/51.55        | ~ (v1_relat_1 @ sk_E)
% 51.33/51.55        | ((sk_C) = (k1_xboole_0)))),
% 51.33/51.55      inference('sup-', [status(thm)], ['43', '71'])).
% 51.33/51.55  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('74', plain,
% 51.33/51.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 51.33/51.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.33/51.55  thf('75', plain,
% 51.33/51.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.33/51.55         ((v1_relat_1 @ X16)
% 51.33/51.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 51.33/51.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 51.33/51.55  thf('76', plain, ((v1_relat_1 @ sk_E)),
% 51.33/51.55      inference('sup-', [status(thm)], ['74', '75'])).
% 51.33/51.55  thf('77', plain,
% 51.33/51.55      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 51.33/51.55          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 51.33/51.55        | ((sk_C) = (k1_xboole_0)))),
% 51.33/51.55      inference('demod', [status(thm)], ['72', '73', '76'])).
% 51.33/51.55  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 51.33/51.55      inference('simplify', [status(thm)], ['77'])).
% 51.33/51.55  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 51.33/51.55      inference('sup-', [status(thm)], ['12', '15'])).
% 51.33/51.55  thf('80', plain, ($false),
% 51.33/51.55      inference('demod', [status(thm)], ['0', '78', '79'])).
% 51.33/51.55  
% 51.33/51.55  % SZS output end Refutation
% 51.33/51.55  
% 51.33/51.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
