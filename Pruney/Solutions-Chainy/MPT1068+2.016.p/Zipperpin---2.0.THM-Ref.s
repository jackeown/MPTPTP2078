%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2lg7YbL7yH

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:59 EST 2020

% Result     : Theorem 4.10s
% Output     : Refutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 166 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          : 1000 (3403 expanded)
%              Number of equality atoms :   62 ( 157 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['17','26'])).

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

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k1_funct_1 @ X4 @ ( k1_funct_1 @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['10','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
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

thf('42',plain,(
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

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','56','57','58','59'])).

thf('61',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','67'])).

thf('69',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2lg7YbL7yH
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.10/4.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.10/4.32  % Solved by: fo/fo7.sh
% 4.10/4.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.10/4.32  % done 2205 iterations in 3.867s
% 4.10/4.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.10/4.32  % SZS output start Refutation
% 4.10/4.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.10/4.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.10/4.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.10/4.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.10/4.32  thf(sk_E_type, type, sk_E: $i).
% 4.10/4.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.10/4.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.10/4.32  thf(sk_B_type, type, sk_B: $i).
% 4.10/4.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.10/4.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.10/4.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.10/4.32  thf(sk_F_type, type, sk_F: $i).
% 4.10/4.32  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.10/4.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.10/4.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.10/4.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.10/4.32  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 4.10/4.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.10/4.32  thf(sk_C_type, type, sk_C: $i).
% 4.10/4.32  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.10/4.32  thf(sk_D_type, type, sk_D: $i).
% 4.10/4.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.10/4.32  thf(sk_A_type, type, sk_A: $i).
% 4.10/4.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.10/4.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.10/4.32  thf(t185_funct_2, conjecture,
% 4.10/4.32    (![A:$i,B:$i,C:$i]:
% 4.10/4.32     ( ( ~( v1_xboole_0 @ C ) ) =>
% 4.10/4.32       ( ![D:$i]:
% 4.10/4.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 4.10/4.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.10/4.32           ( ![E:$i]:
% 4.10/4.32             ( ( ( v1_funct_1 @ E ) & 
% 4.10/4.32                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 4.10/4.32               ( ![F:$i]:
% 4.10/4.32                 ( ( m1_subset_1 @ F @ B ) =>
% 4.10/4.32                   ( ( r1_tarski @
% 4.10/4.32                       ( k2_relset_1 @ B @ C @ D ) @ 
% 4.10/4.32                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 4.10/4.32                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.10/4.32                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 4.10/4.32                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.10/4.32  thf(zf_stmt_0, negated_conjecture,
% 4.10/4.32    (~( ![A:$i,B:$i,C:$i]:
% 4.10/4.32        ( ( ~( v1_xboole_0 @ C ) ) =>
% 4.10/4.32          ( ![D:$i]:
% 4.10/4.32            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 4.10/4.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.10/4.32              ( ![E:$i]:
% 4.10/4.32                ( ( ( v1_funct_1 @ E ) & 
% 4.10/4.32                    ( m1_subset_1 @
% 4.10/4.32                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 4.10/4.32                  ( ![F:$i]:
% 4.10/4.32                    ( ( m1_subset_1 @ F @ B ) =>
% 4.10/4.32                      ( ( r1_tarski @
% 4.10/4.32                          ( k2_relset_1 @ B @ C @ D ) @ 
% 4.10/4.32                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 4.10/4.32                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.10/4.32                          ( ( k1_funct_1 @
% 4.10/4.32                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 4.10/4.32                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 4.10/4.32    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 4.10/4.32  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(t2_subset, axiom,
% 4.10/4.32    (![A:$i,B:$i]:
% 4.10/4.32     ( ( m1_subset_1 @ A @ B ) =>
% 4.10/4.32       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 4.10/4.32  thf('2', plain,
% 4.10/4.32      (![X2 : $i, X3 : $i]:
% 4.10/4.32         ((r2_hidden @ X2 @ X3)
% 4.10/4.32          | (v1_xboole_0 @ X3)
% 4.10/4.32          | ~ (m1_subset_1 @ X2 @ X3))),
% 4.10/4.32      inference('cnf', [status(esa)], [t2_subset])).
% 4.10/4.32  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 4.10/4.32      inference('sup-', [status(thm)], ['1', '2'])).
% 4.10/4.32  thf(t8_boole, axiom,
% 4.10/4.32    (![A:$i,B:$i]:
% 4.10/4.32     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.10/4.32  thf('4', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i]:
% 4.10/4.32         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 4.10/4.32      inference('cnf', [status(esa)], [t8_boole])).
% 4.10/4.32  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('6', plain,
% 4.10/4.32      (![X0 : $i]:
% 4.10/4.32         (((X0) != (k1_xboole_0))
% 4.10/4.32          | ~ (v1_xboole_0 @ sk_B)
% 4.10/4.32          | ~ (v1_xboole_0 @ X0))),
% 4.10/4.32      inference('sup-', [status(thm)], ['4', '5'])).
% 4.10/4.32  thf('7', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 4.10/4.32      inference('simplify', [status(thm)], ['6'])).
% 4.10/4.32  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.10/4.32  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.10/4.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.10/4.32  thf('9', plain, (~ (v1_xboole_0 @ sk_B)),
% 4.10/4.32      inference('simplify_reflect+', [status(thm)], ['7', '8'])).
% 4.10/4.32  thf('10', plain, ((r2_hidden @ sk_F @ sk_B)),
% 4.10/4.32      inference('clc', [status(thm)], ['3', '9'])).
% 4.10/4.32  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(d1_funct_2, axiom,
% 4.10/4.32    (![A:$i,B:$i,C:$i]:
% 4.10/4.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.32       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.10/4.32           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.10/4.32             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.10/4.32         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.10/4.32           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.10/4.32             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.10/4.32  thf(zf_stmt_1, axiom,
% 4.10/4.32    (![C:$i,B:$i,A:$i]:
% 4.10/4.32     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.10/4.32       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.10/4.32  thf('12', plain,
% 4.10/4.32      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.10/4.32         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 4.10/4.32          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 4.10/4.32          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.10/4.32  thf('13', plain,
% 4.10/4.32      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 4.10/4.32        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 4.10/4.32      inference('sup-', [status(thm)], ['11', '12'])).
% 4.10/4.32  thf('14', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(redefinition_k1_relset_1, axiom,
% 4.10/4.32    (![A:$i,B:$i,C:$i]:
% 4.10/4.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.32       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.10/4.32  thf('15', plain,
% 4.10/4.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.10/4.32         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 4.10/4.32          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.10/4.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.10/4.32  thf('16', plain,
% 4.10/4.32      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.10/4.32      inference('sup-', [status(thm)], ['14', '15'])).
% 4.10/4.32  thf('17', plain,
% 4.10/4.32      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 4.10/4.32      inference('demod', [status(thm)], ['13', '16'])).
% 4.10/4.32  thf('18', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.10/4.32  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.10/4.32  thf(zf_stmt_4, axiom,
% 4.10/4.32    (![B:$i,A:$i]:
% 4.10/4.32     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.10/4.32       ( zip_tseitin_0 @ B @ A ) ))).
% 4.10/4.32  thf(zf_stmt_5, axiom,
% 4.10/4.32    (![A:$i,B:$i,C:$i]:
% 4.10/4.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.32       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.10/4.32         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.10/4.32           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.10/4.32             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.10/4.32  thf('19', plain,
% 4.10/4.32      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.10/4.32         (~ (zip_tseitin_0 @ X23 @ X24)
% 4.10/4.32          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 4.10/4.32          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.10/4.32  thf('20', plain,
% 4.10/4.32      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 4.10/4.32      inference('sup-', [status(thm)], ['18', '19'])).
% 4.10/4.32  thf('21', plain,
% 4.10/4.32      (![X18 : $i, X19 : $i]:
% 4.10/4.32         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.10/4.32  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.10/4.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.10/4.32  thf('23', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.10/4.32      inference('sup+', [status(thm)], ['21', '22'])).
% 4.10/4.32  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('25', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 4.10/4.32      inference('sup-', [status(thm)], ['23', '24'])).
% 4.10/4.32  thf('26', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 4.10/4.32      inference('demod', [status(thm)], ['20', '25'])).
% 4.10/4.32  thf('27', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 4.10/4.32      inference('demod', [status(thm)], ['17', '26'])).
% 4.10/4.32  thf(t23_funct_1, axiom,
% 4.10/4.32    (![A:$i,B:$i]:
% 4.10/4.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.10/4.32       ( ![C:$i]:
% 4.10/4.32         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.10/4.32           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 4.10/4.32             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 4.10/4.32               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 4.10/4.32  thf('28', plain,
% 4.10/4.32      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.10/4.32         (~ (v1_relat_1 @ X4)
% 4.10/4.32          | ~ (v1_funct_1 @ X4)
% 4.10/4.32          | ((k1_funct_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 4.10/4.32              = (k1_funct_1 @ X4 @ (k1_funct_1 @ X5 @ X6)))
% 4.10/4.32          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 4.10/4.32          | ~ (v1_funct_1 @ X5)
% 4.10/4.32          | ~ (v1_relat_1 @ X5))),
% 4.10/4.32      inference('cnf', [status(esa)], [t23_funct_1])).
% 4.10/4.32  thf('29', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i]:
% 4.10/4.32         (~ (r2_hidden @ X0 @ sk_B)
% 4.10/4.32          | ~ (v1_relat_1 @ sk_D)
% 4.10/4.32          | ~ (v1_funct_1 @ sk_D)
% 4.10/4.32          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 4.10/4.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 4.10/4.32          | ~ (v1_funct_1 @ X1)
% 4.10/4.32          | ~ (v1_relat_1 @ X1))),
% 4.10/4.32      inference('sup-', [status(thm)], ['27', '28'])).
% 4.10/4.32  thf('30', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(cc1_relset_1, axiom,
% 4.10/4.32    (![A:$i,B:$i,C:$i]:
% 4.10/4.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.32       ( v1_relat_1 @ C ) ))).
% 4.10/4.32  thf('31', plain,
% 4.10/4.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.10/4.32         ((v1_relat_1 @ X7)
% 4.10/4.32          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 4.10/4.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.10/4.32  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 4.10/4.32      inference('sup-', [status(thm)], ['30', '31'])).
% 4.10/4.32  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('34', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i]:
% 4.10/4.32         (~ (r2_hidden @ X0 @ sk_B)
% 4.10/4.32          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 4.10/4.32              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 4.10/4.32          | ~ (v1_funct_1 @ X1)
% 4.10/4.32          | ~ (v1_relat_1 @ X1))),
% 4.10/4.32      inference('demod', [status(thm)], ['29', '32', '33'])).
% 4.10/4.32  thf('35', plain,
% 4.10/4.32      (![X0 : $i]:
% 4.10/4.32         (~ (v1_relat_1 @ X0)
% 4.10/4.32          | ~ (v1_funct_1 @ X0)
% 4.10/4.32          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 4.10/4.32              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F))))),
% 4.10/4.32      inference('sup-', [status(thm)], ['10', '34'])).
% 4.10/4.32  thf('36', plain,
% 4.10/4.32      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 4.10/4.32        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('37', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('38', plain,
% 4.10/4.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.10/4.32         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 4.10/4.32          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.10/4.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.10/4.32  thf('39', plain,
% 4.10/4.32      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 4.10/4.32      inference('sup-', [status(thm)], ['37', '38'])).
% 4.10/4.32  thf('40', plain,
% 4.10/4.32      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 4.10/4.32      inference('demod', [status(thm)], ['36', '39'])).
% 4.10/4.32  thf('41', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(d12_funct_2, axiom,
% 4.10/4.32    (![A:$i,B:$i,C:$i,D:$i]:
% 4.10/4.32     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.10/4.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.10/4.32       ( ![E:$i]:
% 4.10/4.32         ( ( ( v1_funct_1 @ E ) & 
% 4.10/4.32             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.10/4.32           ( ( r1_tarski @
% 4.10/4.32               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 4.10/4.32             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.10/4.32               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 4.10/4.32                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 4.10/4.32  thf('42', plain,
% 4.10/4.32      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.10/4.32         (~ (v1_funct_1 @ X13)
% 4.10/4.32          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 4.10/4.32          | ((k8_funct_2 @ X16 @ X14 @ X15 @ X17 @ X13)
% 4.10/4.32              = (k1_partfun1 @ X16 @ X14 @ X14 @ X15 @ X17 @ X13))
% 4.10/4.32          | ~ (r1_tarski @ (k2_relset_1 @ X16 @ X14 @ X17) @ 
% 4.10/4.32               (k1_relset_1 @ X14 @ X15 @ X13))
% 4.10/4.32          | ((X14) = (k1_xboole_0))
% 4.10/4.32          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 4.10/4.32          | ~ (v1_funct_2 @ X17 @ X16 @ X14)
% 4.10/4.32          | ~ (v1_funct_1 @ X17))),
% 4.10/4.32      inference('cnf', [status(esa)], [d12_funct_2])).
% 4.10/4.32  thf('43', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i]:
% 4.10/4.32         (~ (v1_funct_1 @ X0)
% 4.10/4.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 4.10/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 4.10/4.32          | ((sk_C) = (k1_xboole_0))
% 4.10/4.32          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 4.10/4.32               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 4.10/4.32          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 4.10/4.32              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 4.10/4.32          | ~ (v1_funct_1 @ sk_E))),
% 4.10/4.32      inference('sup-', [status(thm)], ['41', '42'])).
% 4.10/4.32  thf('44', plain,
% 4.10/4.32      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 4.10/4.32      inference('sup-', [status(thm)], ['37', '38'])).
% 4.10/4.32  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('46', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i]:
% 4.10/4.32         (~ (v1_funct_1 @ X0)
% 4.10/4.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 4.10/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 4.10/4.32          | ((sk_C) = (k1_xboole_0))
% 4.10/4.32          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 4.10/4.32          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 4.10/4.32              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 4.10/4.32      inference('demod', [status(thm)], ['43', '44', '45'])).
% 4.10/4.32  thf('47', plain,
% 4.10/4.32      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 4.10/4.32          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 4.10/4.32        | ((sk_C) = (k1_xboole_0))
% 4.10/4.32        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 4.10/4.32        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 4.10/4.32        | ~ (v1_funct_1 @ sk_D))),
% 4.10/4.32      inference('sup-', [status(thm)], ['40', '46'])).
% 4.10/4.32  thf('48', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('49', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf(redefinition_k1_partfun1, axiom,
% 4.10/4.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.10/4.32     ( ( ( v1_funct_1 @ E ) & 
% 4.10/4.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.10/4.32         ( v1_funct_1 @ F ) & 
% 4.10/4.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.10/4.32       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.10/4.32  thf('50', plain,
% 4.10/4.32      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.10/4.32         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 4.10/4.32          | ~ (v1_funct_1 @ X26)
% 4.10/4.32          | ~ (v1_funct_1 @ X29)
% 4.10/4.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 4.10/4.32          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 4.10/4.32              = (k5_relat_1 @ X26 @ X29)))),
% 4.10/4.32      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.10/4.32  thf('51', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.32         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 4.10/4.32            = (k5_relat_1 @ sk_D @ X0))
% 4.10/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.10/4.32          | ~ (v1_funct_1 @ X0)
% 4.10/4.32          | ~ (v1_funct_1 @ sk_D))),
% 4.10/4.32      inference('sup-', [status(thm)], ['49', '50'])).
% 4.10/4.32  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('53', plain,
% 4.10/4.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.32         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 4.10/4.32            = (k5_relat_1 @ sk_D @ X0))
% 4.10/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.10/4.32          | ~ (v1_funct_1 @ X0))),
% 4.10/4.32      inference('demod', [status(thm)], ['51', '52'])).
% 4.10/4.32  thf('54', plain,
% 4.10/4.32      ((~ (v1_funct_1 @ sk_E)
% 4.10/4.32        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 4.10/4.32            = (k5_relat_1 @ sk_D @ sk_E)))),
% 4.10/4.32      inference('sup-', [status(thm)], ['48', '53'])).
% 4.10/4.32  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('56', plain,
% 4.10/4.32      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 4.10/4.32         = (k5_relat_1 @ sk_D @ sk_E))),
% 4.10/4.32      inference('demod', [status(thm)], ['54', '55'])).
% 4.10/4.32  thf('57', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('60', plain,
% 4.10/4.32      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 4.10/4.32          = (k5_relat_1 @ sk_D @ sk_E))
% 4.10/4.32        | ((sk_C) = (k1_xboole_0)))),
% 4.10/4.32      inference('demod', [status(thm)], ['47', '56', '57', '58', '59'])).
% 4.10/4.32  thf('61', plain,
% 4.10/4.32      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 4.10/4.32         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('62', plain,
% 4.10/4.32      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 4.10/4.32          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 4.10/4.32        | ((sk_C) = (k1_xboole_0)))),
% 4.10/4.32      inference('sup-', [status(thm)], ['60', '61'])).
% 4.10/4.32  thf('63', plain,
% 4.10/4.32      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 4.10/4.32          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 4.10/4.32        | ~ (v1_funct_1 @ sk_E)
% 4.10/4.32        | ~ (v1_relat_1 @ sk_E)
% 4.10/4.32        | ((sk_C) = (k1_xboole_0)))),
% 4.10/4.32      inference('sup-', [status(thm)], ['35', '62'])).
% 4.10/4.32  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('65', plain,
% 4.10/4.32      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.10/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.32  thf('66', plain,
% 4.10/4.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.10/4.32         ((v1_relat_1 @ X7)
% 4.10/4.32          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 4.10/4.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.10/4.32  thf('67', plain, ((v1_relat_1 @ sk_E)),
% 4.10/4.32      inference('sup-', [status(thm)], ['65', '66'])).
% 4.10/4.32  thf('68', plain,
% 4.10/4.32      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 4.10/4.32          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 4.10/4.32        | ((sk_C) = (k1_xboole_0)))),
% 4.10/4.32      inference('demod', [status(thm)], ['63', '64', '67'])).
% 4.10/4.32  thf('69', plain, (((sk_C) = (k1_xboole_0))),
% 4.10/4.32      inference('simplify', [status(thm)], ['68'])).
% 4.10/4.32  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.10/4.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.10/4.32  thf('71', plain, ($false),
% 4.10/4.32      inference('demod', [status(thm)], ['0', '69', '70'])).
% 4.10/4.32  
% 4.10/4.32  % SZS output end Refutation
% 4.10/4.32  
% 4.10/4.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
