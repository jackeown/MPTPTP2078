%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7h1ste3BrZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:00 EST 2020

% Result     : Theorem 3.74s
% Output     : Refutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 171 expanded)
%              Number of leaves         :   41 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          : 1016 (3423 expanded)
%              Number of equality atoms :   61 ( 156 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','22','25'])).

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

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k1_funct_1 @ X8 @ ( k1_funct_1 @ X9 @ X10 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['10','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_funct_2 @ X17 @ X15 @ X16 @ X18 @ X14 )
        = ( k1_partfun1 @ X17 @ X15 @ X15 @ X16 @ X18 @ X14 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X17 @ X15 @ X18 ) @ ( k1_relset_1 @ X15 @ X16 @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','57','58','59','60'])).

thf('62',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('70',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','70'])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7h1ste3BrZ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.74/3.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.74/3.95  % Solved by: fo/fo7.sh
% 3.74/3.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.74/3.95  % done 2395 iterations in 3.513s
% 3.74/3.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.74/3.95  % SZS output start Refutation
% 3.74/3.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.74/3.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.74/3.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.74/3.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.74/3.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.74/3.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.74/3.95  thf(sk_B_type, type, sk_B: $i).
% 3.74/3.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.74/3.95  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 3.74/3.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.74/3.95  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.74/3.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.74/3.95  thf(sk_D_type, type, sk_D: $i).
% 3.74/3.95  thf(sk_C_type, type, sk_C: $i).
% 3.74/3.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.74/3.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.74/3.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.74/3.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.74/3.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.74/3.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.74/3.95  thf(sk_A_type, type, sk_A: $i).
% 3.74/3.95  thf(sk_F_type, type, sk_F: $i).
% 3.74/3.95  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.74/3.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.74/3.95  thf(sk_E_type, type, sk_E: $i).
% 3.74/3.95  thf(t185_funct_2, conjecture,
% 3.74/3.95    (![A:$i,B:$i,C:$i]:
% 3.74/3.95     ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.74/3.95       ( ![D:$i]:
% 3.74/3.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.74/3.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.74/3.95           ( ![E:$i]:
% 3.74/3.95             ( ( ( v1_funct_1 @ E ) & 
% 3.74/3.95                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.74/3.95               ( ![F:$i]:
% 3.74/3.95                 ( ( m1_subset_1 @ F @ B ) =>
% 3.74/3.95                   ( ( r1_tarski @
% 3.74/3.95                       ( k2_relset_1 @ B @ C @ D ) @ 
% 3.74/3.95                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.74/3.95                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.74/3.95                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.74/3.95                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.74/3.95  thf(zf_stmt_0, negated_conjecture,
% 3.74/3.95    (~( ![A:$i,B:$i,C:$i]:
% 3.74/3.95        ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.74/3.95          ( ![D:$i]:
% 3.74/3.95            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.74/3.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.74/3.95              ( ![E:$i]:
% 3.74/3.95                ( ( ( v1_funct_1 @ E ) & 
% 3.74/3.95                    ( m1_subset_1 @
% 3.74/3.95                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.74/3.95                  ( ![F:$i]:
% 3.74/3.95                    ( ( m1_subset_1 @ F @ B ) =>
% 3.74/3.95                      ( ( r1_tarski @
% 3.74/3.95                          ( k2_relset_1 @ B @ C @ D ) @ 
% 3.74/3.95                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.74/3.95                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.74/3.95                          ( ( k1_funct_1 @
% 3.74/3.95                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.74/3.95                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.74/3.95    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 3.74/3.95  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(t2_subset, axiom,
% 3.74/3.95    (![A:$i,B:$i]:
% 3.74/3.95     ( ( m1_subset_1 @ A @ B ) =>
% 3.74/3.95       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.74/3.95  thf('2', plain,
% 3.74/3.95      (![X2 : $i, X3 : $i]:
% 3.74/3.95         ((r2_hidden @ X2 @ X3)
% 3.74/3.95          | (v1_xboole_0 @ X3)
% 3.74/3.95          | ~ (m1_subset_1 @ X2 @ X3))),
% 3.74/3.95      inference('cnf', [status(esa)], [t2_subset])).
% 3.74/3.95  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 3.74/3.95      inference('sup-', [status(thm)], ['1', '2'])).
% 3.74/3.95  thf(t8_boole, axiom,
% 3.74/3.95    (![A:$i,B:$i]:
% 3.74/3.95     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.74/3.95  thf('4', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.74/3.95      inference('cnf', [status(esa)], [t8_boole])).
% 3.74/3.95  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('6', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (((X0) != (k1_xboole_0))
% 3.74/3.95          | ~ (v1_xboole_0 @ sk_B)
% 3.74/3.95          | ~ (v1_xboole_0 @ X0))),
% 3.74/3.95      inference('sup-', [status(thm)], ['4', '5'])).
% 3.74/3.95  thf('7', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 3.74/3.95      inference('simplify', [status(thm)], ['6'])).
% 3.74/3.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.74/3.95  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/3.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/3.95  thf('9', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.74/3.95      inference('simplify_reflect+', [status(thm)], ['7', '8'])).
% 3.74/3.95  thf('10', plain, ((r2_hidden @ sk_F @ sk_B)),
% 3.74/3.95      inference('clc', [status(thm)], ['3', '9'])).
% 3.74/3.95  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(d1_funct_2, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i]:
% 3.74/3.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.74/3.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.74/3.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.74/3.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.74/3.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.74/3.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.74/3.95  thf(zf_stmt_1, axiom,
% 3.74/3.95    (![C:$i,B:$i,A:$i]:
% 3.74/3.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.74/3.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.74/3.95  thf('12', plain,
% 3.74/3.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.74/3.95         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 3.74/3.95          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 3.74/3.95          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/3.95  thf('13', plain,
% 3.74/3.95      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 3.74/3.95        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['11', '12'])).
% 3.74/3.95  thf('14', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.74/3.95  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.74/3.95  thf(zf_stmt_4, axiom,
% 3.74/3.95    (![B:$i,A:$i]:
% 3.74/3.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.74/3.95       ( zip_tseitin_0 @ B @ A ) ))).
% 3.74/3.95  thf(zf_stmt_5, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i]:
% 3.74/3.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.74/3.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.74/3.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.74/3.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.74/3.95  thf('15', plain,
% 3.74/3.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.74/3.95         (~ (zip_tseitin_0 @ X24 @ X25)
% 3.74/3.95          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 3.74/3.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/3.95  thf('16', plain,
% 3.74/3.95      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 3.74/3.95      inference('sup-', [status(thm)], ['14', '15'])).
% 3.74/3.95  thf('17', plain,
% 3.74/3.95      (![X19 : $i, X20 : $i]:
% 3.74/3.95         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.74/3.95  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/3.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/3.95  thf('19', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.74/3.95      inference('sup+', [status(thm)], ['17', '18'])).
% 3.74/3.95  thf('20', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('21', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 3.74/3.95      inference('sup-', [status(thm)], ['19', '20'])).
% 3.74/3.95  thf('22', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 3.74/3.95      inference('demod', [status(thm)], ['16', '21'])).
% 3.74/3.95  thf('23', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(redefinition_k1_relset_1, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i]:
% 3.74/3.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/3.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.74/3.95  thf('24', plain,
% 3.74/3.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.74/3.95         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 3.74/3.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.74/3.95  thf('25', plain,
% 3.74/3.95      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.74/3.95      inference('sup-', [status(thm)], ['23', '24'])).
% 3.74/3.95  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.74/3.95      inference('demod', [status(thm)], ['13', '22', '25'])).
% 3.74/3.95  thf(t23_funct_1, axiom,
% 3.74/3.95    (![A:$i,B:$i]:
% 3.74/3.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.74/3.95       ( ![C:$i]:
% 3.74/3.95         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.74/3.95           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.74/3.95             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.74/3.95               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 3.74/3.95  thf('27', plain,
% 3.74/3.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.74/3.95         (~ (v1_relat_1 @ X8)
% 3.74/3.95          | ~ (v1_funct_1 @ X8)
% 3.74/3.95          | ((k1_funct_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 3.74/3.95              = (k1_funct_1 @ X8 @ (k1_funct_1 @ X9 @ X10)))
% 3.74/3.95          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 3.74/3.95          | ~ (v1_funct_1 @ X9)
% 3.74/3.95          | ~ (v1_relat_1 @ X9))),
% 3.74/3.95      inference('cnf', [status(esa)], [t23_funct_1])).
% 3.74/3.95  thf('28', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (r2_hidden @ X0 @ sk_B)
% 3.74/3.95          | ~ (v1_relat_1 @ sk_D)
% 3.74/3.95          | ~ (v1_funct_1 @ sk_D)
% 3.74/3.95          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 3.74/3.95              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 3.74/3.95          | ~ (v1_funct_1 @ X1)
% 3.74/3.95          | ~ (v1_relat_1 @ X1))),
% 3.74/3.95      inference('sup-', [status(thm)], ['26', '27'])).
% 3.74/3.95  thf('29', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(cc2_relat_1, axiom,
% 3.74/3.95    (![A:$i]:
% 3.74/3.95     ( ( v1_relat_1 @ A ) =>
% 3.74/3.95       ( ![B:$i]:
% 3.74/3.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.74/3.95  thf('30', plain,
% 3.74/3.95      (![X4 : $i, X5 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.74/3.95          | (v1_relat_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X5))),
% 3.74/3.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.74/3.95  thf('31', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D))),
% 3.74/3.95      inference('sup-', [status(thm)], ['29', '30'])).
% 3.74/3.95  thf(fc6_relat_1, axiom,
% 3.74/3.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.74/3.95  thf('32', plain,
% 3.74/3.95      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.74/3.95  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 3.74/3.95      inference('demod', [status(thm)], ['31', '32'])).
% 3.74/3.95  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('35', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (r2_hidden @ X0 @ sk_B)
% 3.74/3.95          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 3.74/3.95              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 3.74/3.95          | ~ (v1_funct_1 @ X1)
% 3.74/3.95          | ~ (v1_relat_1 @ X1))),
% 3.74/3.95      inference('demod', [status(thm)], ['28', '33', '34'])).
% 3.74/3.95  thf('36', plain,
% 3.74/3.95      (![X0 : $i]:
% 3.74/3.95         (~ (v1_relat_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 3.74/3.95              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F))))),
% 3.74/3.95      inference('sup-', [status(thm)], ['10', '35'])).
% 3.74/3.95  thf('37', plain,
% 3.74/3.95      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 3.74/3.95        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('38', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('39', plain,
% 3.74/3.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.74/3.95         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 3.74/3.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.74/3.95  thf('40', plain,
% 3.74/3.95      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.74/3.95      inference('sup-', [status(thm)], ['38', '39'])).
% 3.74/3.95  thf('41', plain,
% 3.74/3.95      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 3.74/3.95      inference('demod', [status(thm)], ['37', '40'])).
% 3.74/3.95  thf('42', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(d12_funct_2, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i,D:$i]:
% 3.74/3.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.74/3.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/3.95       ( ![E:$i]:
% 3.74/3.95         ( ( ( v1_funct_1 @ E ) & 
% 3.74/3.95             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.74/3.95           ( ( r1_tarski @
% 3.74/3.95               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 3.74/3.95             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.74/3.95               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 3.74/3.95                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 3.74/3.95  thf('43', plain,
% 3.74/3.95      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.74/3.95         (~ (v1_funct_1 @ X14)
% 3.74/3.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 3.74/3.95          | ((k8_funct_2 @ X17 @ X15 @ X16 @ X18 @ X14)
% 3.74/3.95              = (k1_partfun1 @ X17 @ X15 @ X15 @ X16 @ X18 @ X14))
% 3.74/3.95          | ~ (r1_tarski @ (k2_relset_1 @ X17 @ X15 @ X18) @ 
% 3.74/3.95               (k1_relset_1 @ X15 @ X16 @ X14))
% 3.74/3.95          | ((X15) = (k1_xboole_0))
% 3.74/3.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 3.74/3.95          | ~ (v1_funct_2 @ X18 @ X17 @ X15)
% 3.74/3.95          | ~ (v1_funct_1 @ X18))),
% 3.74/3.95      inference('cnf', [status(esa)], [d12_funct_2])).
% 3.74/3.95  thf('44', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 3.74/3.95          | ((sk_C) = (k1_xboole_0))
% 3.74/3.95          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 3.74/3.95               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 3.74/3.95          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 3.74/3.95              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 3.74/3.95          | ~ (v1_funct_1 @ sk_E))),
% 3.74/3.95      inference('sup-', [status(thm)], ['42', '43'])).
% 3.74/3.95  thf('45', plain,
% 3.74/3.95      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.74/3.95      inference('sup-', [status(thm)], ['38', '39'])).
% 3.74/3.95  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('47', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i]:
% 3.74/3.95         (~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 3.74/3.95          | ((sk_C) = (k1_xboole_0))
% 3.74/3.95          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 3.74/3.95          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 3.74/3.95              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 3.74/3.95      inference('demod', [status(thm)], ['44', '45', '46'])).
% 3.74/3.95  thf('48', plain,
% 3.74/3.95      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.74/3.95          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 3.74/3.95        | ((sk_C) = (k1_xboole_0))
% 3.74/3.95        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 3.74/3.95        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 3.74/3.95        | ~ (v1_funct_1 @ sk_D))),
% 3.74/3.95      inference('sup-', [status(thm)], ['41', '47'])).
% 3.74/3.95  thf('49', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('50', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf(redefinition_k1_partfun1, axiom,
% 3.74/3.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.74/3.95     ( ( ( v1_funct_1 @ E ) & 
% 3.74/3.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.74/3.95         ( v1_funct_1 @ F ) & 
% 3.74/3.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.74/3.95       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.74/3.95  thf('51', plain,
% 3.74/3.95      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.74/3.95          | ~ (v1_funct_1 @ X27)
% 3.74/3.95          | ~ (v1_funct_1 @ X30)
% 3.74/3.95          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.74/3.95          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 3.74/3.95              = (k5_relat_1 @ X27 @ X30)))),
% 3.74/3.95      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.74/3.95  thf('52', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.74/3.95         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 3.74/3.95            = (k5_relat_1 @ sk_D @ X0))
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.74/3.95          | ~ (v1_funct_1 @ X0)
% 3.74/3.95          | ~ (v1_funct_1 @ sk_D))),
% 3.74/3.95      inference('sup-', [status(thm)], ['50', '51'])).
% 3.74/3.95  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('54', plain,
% 3.74/3.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.74/3.95         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 3.74/3.95            = (k5_relat_1 @ sk_D @ X0))
% 3.74/3.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.74/3.95          | ~ (v1_funct_1 @ X0))),
% 3.74/3.95      inference('demod', [status(thm)], ['52', '53'])).
% 3.74/3.95  thf('55', plain,
% 3.74/3.95      ((~ (v1_funct_1 @ sk_E)
% 3.74/3.95        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.74/3.95            = (k5_relat_1 @ sk_D @ sk_E)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['49', '54'])).
% 3.74/3.95  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('57', plain,
% 3.74/3.95      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.74/3.95         = (k5_relat_1 @ sk_D @ sk_E))),
% 3.74/3.95      inference('demod', [status(thm)], ['55', '56'])).
% 3.74/3.95  thf('58', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('61', plain,
% 3.74/3.95      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 3.74/3.95          = (k5_relat_1 @ sk_D @ sk_E))
% 3.74/3.95        | ((sk_C) = (k1_xboole_0)))),
% 3.74/3.95      inference('demod', [status(thm)], ['48', '57', '58', '59', '60'])).
% 3.74/3.95  thf('62', plain,
% 3.74/3.95      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 3.74/3.95         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('63', plain,
% 3.74/3.95      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.74/3.95          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 3.74/3.95        | ((sk_C) = (k1_xboole_0)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['61', '62'])).
% 3.74/3.95  thf('64', plain,
% 3.74/3.95      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.74/3.95          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 3.74/3.95        | ~ (v1_funct_1 @ sk_E)
% 3.74/3.95        | ~ (v1_relat_1 @ sk_E)
% 3.74/3.95        | ((sk_C) = (k1_xboole_0)))),
% 3.74/3.95      inference('sup-', [status(thm)], ['36', '63'])).
% 3.74/3.95  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('66', plain,
% 3.74/3.95      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 3.74/3.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/3.95  thf('67', plain,
% 3.74/3.95      (![X4 : $i, X5 : $i]:
% 3.74/3.95         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.74/3.95          | (v1_relat_1 @ X4)
% 3.74/3.95          | ~ (v1_relat_1 @ X5))),
% 3.74/3.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.74/3.95  thf('68', plain,
% 3.74/3.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 3.74/3.95      inference('sup-', [status(thm)], ['66', '67'])).
% 3.74/3.95  thf('69', plain,
% 3.74/3.95      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 3.74/3.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.74/3.95  thf('70', plain, ((v1_relat_1 @ sk_E)),
% 3.74/3.95      inference('demod', [status(thm)], ['68', '69'])).
% 3.74/3.95  thf('71', plain,
% 3.74/3.95      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 3.74/3.95          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 3.74/3.95        | ((sk_C) = (k1_xboole_0)))),
% 3.74/3.95      inference('demod', [status(thm)], ['64', '65', '70'])).
% 3.74/3.95  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 3.74/3.95      inference('simplify', [status(thm)], ['71'])).
% 3.74/3.95  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/3.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/3.95  thf('74', plain, ($false),
% 3.74/3.95      inference('demod', [status(thm)], ['0', '72', '73'])).
% 3.74/3.95  
% 3.74/3.95  % SZS output end Refutation
% 3.74/3.95  
% 3.74/3.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
