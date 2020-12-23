%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yjOITPeHCl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:00 EST 2020

% Result     : Theorem 3.41s
% Output     : Refutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 174 expanded)
%              Number of leaves         :   41 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          : 1024 (3436 expanded)
%              Number of equality atoms :   63 ( 159 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','24','27'])).

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

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['12','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_funct_2 @ X16 @ X14 @ X15 @ X17 @ X13 )
        = ( k1_partfun1 @ X16 @ X14 @ X14 @ X15 @ X17 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X16 @ X14 @ X17 ) @ ( k1_relset_1 @ X14 @ X15 @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','59','60','61','62'])).

thf('64',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','72'])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yjOITPeHCl
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:20:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.41/3.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.41/3.66  % Solved by: fo/fo7.sh
% 3.41/3.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.41/3.66  % done 2224 iterations in 3.193s
% 3.41/3.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.41/3.66  % SZS output start Refutation
% 3.41/3.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.41/3.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.41/3.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.41/3.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.41/3.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.41/3.66  thf(sk_E_type, type, sk_E: $i).
% 3.41/3.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.41/3.66  thf(sk_B_type, type, sk_B: $i).
% 3.41/3.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.41/3.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.41/3.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.41/3.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.41/3.66  thf(sk_F_type, type, sk_F: $i).
% 3.41/3.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.41/3.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.41/3.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.41/3.66  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 3.41/3.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.41/3.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.41/3.66  thf(sk_C_type, type, sk_C: $i).
% 3.41/3.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.41/3.66  thf(sk_D_type, type, sk_D: $i).
% 3.41/3.66  thf(sk_A_type, type, sk_A: $i).
% 3.41/3.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.41/3.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.41/3.66  thf(t185_funct_2, conjecture,
% 3.41/3.66    (![A:$i,B:$i,C:$i]:
% 3.41/3.66     ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.41/3.66       ( ![D:$i]:
% 3.41/3.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.41/3.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.41/3.66           ( ![E:$i]:
% 3.41/3.66             ( ( ( v1_funct_1 @ E ) & 
% 3.41/3.66                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.41/3.66               ( ![F:$i]:
% 3.41/3.66                 ( ( m1_subset_1 @ F @ B ) =>
% 3.41/3.66                   ( ( r1_tarski @
% 3.41/3.66                       ( k2_relset_1 @ B @ C @ D ) @ 
% 3.41/3.66                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.41/3.66                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.41/3.66                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.41/3.66                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.41/3.66  thf(zf_stmt_0, negated_conjecture,
% 3.41/3.66    (~( ![A:$i,B:$i,C:$i]:
% 3.41/3.66        ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.41/3.66          ( ![D:$i]:
% 3.41/3.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.41/3.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.41/3.66              ( ![E:$i]:
% 3.41/3.66                ( ( ( v1_funct_1 @ E ) & 
% 3.41/3.66                    ( m1_subset_1 @
% 3.41/3.66                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.41/3.66                  ( ![F:$i]:
% 3.41/3.66                    ( ( m1_subset_1 @ F @ B ) =>
% 3.41/3.66                      ( ( r1_tarski @
% 3.41/3.66                          ( k2_relset_1 @ B @ C @ D ) @ 
% 3.41/3.66                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.41/3.66                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.41/3.66                          ( ( k1_funct_1 @
% 3.41/3.66                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.41/3.66                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.41/3.66    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 3.41/3.66  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(t2_subset, axiom,
% 3.41/3.66    (![A:$i,B:$i]:
% 3.41/3.66     ( ( m1_subset_1 @ A @ B ) =>
% 3.41/3.66       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.41/3.66  thf('2', plain,
% 3.41/3.66      (![X1 : $i, X2 : $i]:
% 3.41/3.66         ((r2_hidden @ X1 @ X2)
% 3.41/3.66          | (v1_xboole_0 @ X2)
% 3.41/3.66          | ~ (m1_subset_1 @ X1 @ X2))),
% 3.41/3.66      inference('cnf', [status(esa)], [t2_subset])).
% 3.41/3.66  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 3.41/3.66      inference('sup-', [status(thm)], ['1', '2'])).
% 3.41/3.66  thf(l13_xboole_0, axiom,
% 3.41/3.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.41/3.66  thf('4', plain,
% 3.41/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.41/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.41/3.66  thf('5', plain,
% 3.41/3.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.41/3.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.41/3.66  thf('6', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i]:
% 3.41/3.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.41/3.66      inference('sup+', [status(thm)], ['4', '5'])).
% 3.41/3.66  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('8', plain,
% 3.41/3.66      (![X0 : $i]:
% 3.41/3.66         (((X0) != (k1_xboole_0))
% 3.41/3.66          | ~ (v1_xboole_0 @ X0)
% 3.41/3.66          | ~ (v1_xboole_0 @ sk_B))),
% 3.41/3.66      inference('sup-', [status(thm)], ['6', '7'])).
% 3.41/3.66  thf('9', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.41/3.66      inference('simplify', [status(thm)], ['8'])).
% 3.41/3.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.41/3.66  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.41/3.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.41/3.66  thf('11', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.41/3.66      inference('simplify_reflect+', [status(thm)], ['9', '10'])).
% 3.41/3.66  thf('12', plain, ((r2_hidden @ sk_F @ sk_B)),
% 3.41/3.66      inference('clc', [status(thm)], ['3', '11'])).
% 3.41/3.66  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(d1_funct_2, axiom,
% 3.41/3.66    (![A:$i,B:$i,C:$i]:
% 3.41/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.41/3.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.41/3.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.41/3.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.41/3.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.41/3.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.41/3.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.41/3.66  thf(zf_stmt_1, axiom,
% 3.41/3.66    (![C:$i,B:$i,A:$i]:
% 3.41/3.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.41/3.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.41/3.66  thf('14', plain,
% 3.41/3.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.41/3.66         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 3.41/3.66          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 3.41/3.66          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.41/3.66  thf('15', plain,
% 3.41/3.66      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 3.41/3.66        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 3.41/3.66      inference('sup-', [status(thm)], ['13', '14'])).
% 3.41/3.66  thf('16', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.41/3.66  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.41/3.66  thf(zf_stmt_4, axiom,
% 3.41/3.66    (![B:$i,A:$i]:
% 3.41/3.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.41/3.66       ( zip_tseitin_0 @ B @ A ) ))).
% 3.41/3.66  thf(zf_stmt_5, axiom,
% 3.41/3.66    (![A:$i,B:$i,C:$i]:
% 3.41/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.41/3.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.41/3.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.41/3.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.41/3.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.41/3.66  thf('17', plain,
% 3.41/3.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.41/3.66         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.41/3.66          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.41/3.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.41/3.66  thf('18', plain,
% 3.41/3.66      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.41/3.66      inference('sup-', [status(thm)], ['16', '17'])).
% 3.41/3.66  thf('19', plain,
% 3.41/3.66      (![X18 : $i, X19 : $i]:
% 3.41/3.66         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.41/3.66  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.41/3.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.41/3.66  thf('21', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.41/3.66      inference('sup+', [status(thm)], ['19', '20'])).
% 3.41/3.66  thf('22', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('23', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 3.41/3.66      inference('sup-', [status(thm)], ['21', '22'])).
% 3.41/3.66  thf('24', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 3.41/3.66      inference('demod', [status(thm)], ['18', '23'])).
% 3.41/3.66  thf('25', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(redefinition_k1_relset_1, axiom,
% 3.41/3.66    (![A:$i,B:$i,C:$i]:
% 3.41/3.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.41/3.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.41/3.66  thf('26', plain,
% 3.41/3.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.41/3.66         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 3.41/3.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.41/3.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.41/3.66  thf('27', plain,
% 3.41/3.66      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.41/3.66      inference('sup-', [status(thm)], ['25', '26'])).
% 3.41/3.66  thf('28', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.41/3.66      inference('demod', [status(thm)], ['15', '24', '27'])).
% 3.41/3.66  thf(t23_funct_1, axiom,
% 3.41/3.66    (![A:$i,B:$i]:
% 3.41/3.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.41/3.66       ( ![C:$i]:
% 3.41/3.66         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.41/3.66           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.41/3.66             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.41/3.66               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 3.41/3.66  thf('29', plain,
% 3.41/3.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.41/3.66         (~ (v1_relat_1 @ X7)
% 3.41/3.66          | ~ (v1_funct_1 @ X7)
% 3.41/3.66          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 3.41/3.66              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 3.41/3.66          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 3.41/3.66          | ~ (v1_funct_1 @ X8)
% 3.41/3.66          | ~ (v1_relat_1 @ X8))),
% 3.41/3.66      inference('cnf', [status(esa)], [t23_funct_1])).
% 3.41/3.66  thf('30', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i]:
% 3.41/3.66         (~ (r2_hidden @ X0 @ sk_B)
% 3.41/3.66          | ~ (v1_relat_1 @ sk_D)
% 3.41/3.66          | ~ (v1_funct_1 @ sk_D)
% 3.41/3.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 3.41/3.66              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 3.41/3.66          | ~ (v1_funct_1 @ X1)
% 3.41/3.66          | ~ (v1_relat_1 @ X1))),
% 3.41/3.66      inference('sup-', [status(thm)], ['28', '29'])).
% 3.41/3.66  thf('31', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(cc2_relat_1, axiom,
% 3.41/3.66    (![A:$i]:
% 3.41/3.66     ( ( v1_relat_1 @ A ) =>
% 3.41/3.66       ( ![B:$i]:
% 3.41/3.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.41/3.66  thf('32', plain,
% 3.41/3.66      (![X3 : $i, X4 : $i]:
% 3.41/3.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.41/3.66          | (v1_relat_1 @ X3)
% 3.41/3.66          | ~ (v1_relat_1 @ X4))),
% 3.41/3.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.41/3.66  thf('33', plain,
% 3.41/3.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D))),
% 3.41/3.66      inference('sup-', [status(thm)], ['31', '32'])).
% 3.41/3.66  thf(fc6_relat_1, axiom,
% 3.41/3.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.41/3.66  thf('34', plain,
% 3.41/3.66      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 3.41/3.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.41/3.66  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 3.41/3.66      inference('demod', [status(thm)], ['33', '34'])).
% 3.41/3.66  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('37', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i]:
% 3.41/3.66         (~ (r2_hidden @ X0 @ sk_B)
% 3.41/3.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 3.41/3.66              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 3.41/3.66          | ~ (v1_funct_1 @ X1)
% 3.41/3.66          | ~ (v1_relat_1 @ X1))),
% 3.41/3.66      inference('demod', [status(thm)], ['30', '35', '36'])).
% 3.41/3.66  thf('38', plain,
% 3.41/3.66      (![X0 : $i]:
% 3.41/3.66         (~ (v1_relat_1 @ X0)
% 3.41/3.66          | ~ (v1_funct_1 @ X0)
% 3.41/3.66          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 3.41/3.66              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F))))),
% 3.41/3.66      inference('sup-', [status(thm)], ['12', '37'])).
% 3.41/3.66  thf('39', plain,
% 3.41/3.66      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 3.41/3.66        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('40', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('41', plain,
% 3.41/3.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.41/3.66         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 3.41/3.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.41/3.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.41/3.66  thf('42', plain,
% 3.41/3.66      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.41/3.66      inference('sup-', [status(thm)], ['40', '41'])).
% 3.41/3.66  thf('43', plain,
% 3.41/3.66      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 3.41/3.66      inference('demod', [status(thm)], ['39', '42'])).
% 3.41/3.66  thf('44', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(d12_funct_2, axiom,
% 3.41/3.66    (![A:$i,B:$i,C:$i,D:$i]:
% 3.41/3.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.41/3.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.41/3.66       ( ![E:$i]:
% 3.41/3.66         ( ( ( v1_funct_1 @ E ) & 
% 3.41/3.66             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.41/3.66           ( ( r1_tarski @
% 3.41/3.66               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 3.41/3.66             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.41/3.66               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 3.41/3.66                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 3.41/3.66  thf('45', plain,
% 3.41/3.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 3.41/3.66         (~ (v1_funct_1 @ X13)
% 3.41/3.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 3.41/3.66          | ((k8_funct_2 @ X16 @ X14 @ X15 @ X17 @ X13)
% 3.41/3.66              = (k1_partfun1 @ X16 @ X14 @ X14 @ X15 @ X17 @ X13))
% 3.41/3.66          | ~ (r1_tarski @ (k2_relset_1 @ X16 @ X14 @ X17) @ 
% 3.41/3.66               (k1_relset_1 @ X14 @ X15 @ X13))
% 3.41/3.66          | ((X14) = (k1_xboole_0))
% 3.41/3.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 3.41/3.66          | ~ (v1_funct_2 @ X17 @ X16 @ X14)
% 3.41/3.66          | ~ (v1_funct_1 @ X17))),
% 3.41/3.66      inference('cnf', [status(esa)], [d12_funct_2])).
% 3.41/3.66  thf('46', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i]:
% 3.41/3.66         (~ (v1_funct_1 @ X0)
% 3.41/3.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 3.41/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 3.41/3.66          | ((sk_C) = (k1_xboole_0))
% 3.41/3.66          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 3.41/3.66               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 3.41/3.66          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 3.41/3.66              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 3.41/3.66          | ~ (v1_funct_1 @ sk_E))),
% 3.41/3.66      inference('sup-', [status(thm)], ['44', '45'])).
% 3.41/3.66  thf('47', plain,
% 3.41/3.66      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.41/3.66      inference('sup-', [status(thm)], ['40', '41'])).
% 3.41/3.66  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('49', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i]:
% 3.41/3.66         (~ (v1_funct_1 @ X0)
% 3.41/3.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 3.41/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 3.41/3.66          | ((sk_C) = (k1_xboole_0))
% 3.41/3.66          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 3.41/3.66          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 3.41/3.66              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 3.41/3.66      inference('demod', [status(thm)], ['46', '47', '48'])).
% 3.41/3.66  thf('50', plain,
% 3.41/3.66      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.41/3.66          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 3.41/3.66        | ((sk_C) = (k1_xboole_0))
% 3.41/3.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 3.41/3.66        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 3.41/3.66        | ~ (v1_funct_1 @ sk_D))),
% 3.41/3.66      inference('sup-', [status(thm)], ['43', '49'])).
% 3.41/3.66  thf('51', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('52', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf(redefinition_k1_partfun1, axiom,
% 3.41/3.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.41/3.66     ( ( ( v1_funct_1 @ E ) & 
% 3.41/3.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.41/3.66         ( v1_funct_1 @ F ) & 
% 3.41/3.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.41/3.66       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.41/3.66  thf('53', plain,
% 3.41/3.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.41/3.66         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.41/3.66          | ~ (v1_funct_1 @ X26)
% 3.41/3.66          | ~ (v1_funct_1 @ X29)
% 3.41/3.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.41/3.66          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 3.41/3.66              = (k5_relat_1 @ X26 @ X29)))),
% 3.41/3.66      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.41/3.66  thf('54', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.66         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 3.41/3.66            = (k5_relat_1 @ sk_D @ X0))
% 3.41/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.41/3.66          | ~ (v1_funct_1 @ X0)
% 3.41/3.66          | ~ (v1_funct_1 @ sk_D))),
% 3.41/3.66      inference('sup-', [status(thm)], ['52', '53'])).
% 3.41/3.66  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('56', plain,
% 3.41/3.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.41/3.66         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 3.41/3.66            = (k5_relat_1 @ sk_D @ X0))
% 3.41/3.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.41/3.66          | ~ (v1_funct_1 @ X0))),
% 3.41/3.66      inference('demod', [status(thm)], ['54', '55'])).
% 3.41/3.66  thf('57', plain,
% 3.41/3.66      ((~ (v1_funct_1 @ sk_E)
% 3.41/3.66        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.41/3.66            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.41/3.66      inference('sup-', [status(thm)], ['51', '56'])).
% 3.41/3.66  thf('58', plain, ((v1_funct_1 @ sk_E)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('59', plain,
% 3.41/3.66      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.41/3.66         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.41/3.66      inference('demod', [status(thm)], ['57', '58'])).
% 3.41/3.66  thf('60', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('63', plain,
% 3.41/3.66      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.41/3.66          = (k5_relat_1 @ sk_D @ sk_E))
% 3.41/3.66        | ((sk_C) = (k1_xboole_0)))),
% 3.41/3.66      inference('demod', [status(thm)], ['50', '59', '60', '61', '62'])).
% 3.41/3.66  thf('64', plain,
% 3.41/3.66      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 3.41/3.66         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('65', plain,
% 3.41/3.66      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.41/3.66          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 3.41/3.66        | ((sk_C) = (k1_xboole_0)))),
% 3.41/3.66      inference('sup-', [status(thm)], ['63', '64'])).
% 3.41/3.66  thf('66', plain,
% 3.41/3.66      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.41/3.66          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 3.41/3.66        | ~ (v1_funct_1 @ sk_E)
% 3.41/3.66        | ~ (v1_relat_1 @ sk_E)
% 3.41/3.66        | ((sk_C) = (k1_xboole_0)))),
% 3.41/3.66      inference('sup-', [status(thm)], ['38', '65'])).
% 3.41/3.66  thf('67', plain, ((v1_funct_1 @ sk_E)),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('68', plain,
% 3.41/3.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.41/3.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.41/3.66  thf('69', plain,
% 3.41/3.66      (![X3 : $i, X4 : $i]:
% 3.41/3.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.41/3.66          | (v1_relat_1 @ X3)
% 3.41/3.66          | ~ (v1_relat_1 @ X4))),
% 3.41/3.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.41/3.66  thf('70', plain,
% 3.41/3.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 3.41/3.66      inference('sup-', [status(thm)], ['68', '69'])).
% 3.41/3.66  thf('71', plain,
% 3.41/3.66      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 3.41/3.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.41/3.66  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 3.41/3.66      inference('demod', [status(thm)], ['70', '71'])).
% 3.41/3.66  thf('73', plain,
% 3.41/3.66      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.41/3.66          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 3.41/3.66        | ((sk_C) = (k1_xboole_0)))),
% 3.41/3.66      inference('demod', [status(thm)], ['66', '67', '72'])).
% 3.41/3.66  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 3.41/3.66      inference('simplify', [status(thm)], ['73'])).
% 3.41/3.66  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.41/3.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.41/3.66  thf('76', plain, ($false),
% 3.41/3.66      inference('demod', [status(thm)], ['0', '74', '75'])).
% 3.41/3.66  
% 3.41/3.66  % SZS output end Refutation
% 3.41/3.66  
% 3.41/3.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
