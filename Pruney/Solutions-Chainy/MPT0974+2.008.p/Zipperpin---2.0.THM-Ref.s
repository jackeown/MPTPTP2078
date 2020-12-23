%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LTrTWvypBW

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:41 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 140 expanded)
%              Number of leaves         :   37 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  895 (2765 expanded)
%              Number of equality atoms :   61 ( 207 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X9 @ X10 @ X12 @ X13 @ X8 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k4_relset_1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['38','40','45','48'])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['12','49'])).

thf('51',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('54',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LTrTWvypBW
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.03  % Solved by: fo/fo7.sh
% 0.83/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.03  % done 439 iterations in 0.618s
% 0.83/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.03  % SZS output start Refutation
% 0.83/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.83/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.83/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.83/1.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.83/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.83/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.83/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.83/1.03  thf(sk_E_type, type, sk_E: $i).
% 0.83/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.03  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.83/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.03  thf(t20_funct_2, conjecture,
% 0.83/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.83/1.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.03       ( ![E:$i]:
% 0.83/1.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.83/1.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.83/1.03           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.83/1.03               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.83/1.03             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.83/1.03               ( ( k2_relset_1 @
% 0.83/1.03                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.83/1.03                 ( C ) ) ) ) ) ) ))).
% 0.83/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.03    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.03        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.83/1.03            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.03          ( ![E:$i]:
% 0.83/1.03            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.83/1.03                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.83/1.03              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.83/1.03                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.83/1.03                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.83/1.03                  ( ( k2_relset_1 @
% 0.83/1.03                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.83/1.03                    ( C ) ) ) ) ) ) ) )),
% 0.83/1.03    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 0.83/1.03  thf('0', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('1', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(dt_k4_relset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.83/1.03     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.83/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.83/1.03       ( m1_subset_1 @
% 0.83/1.03         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.83/1.03         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.83/1.03  thf('2', plain,
% 0.83/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.83/1.03          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.83/1.03          | (m1_subset_1 @ (k4_relset_1 @ X9 @ X10 @ X12 @ X13 @ X8 @ X11) @ 
% 0.83/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X13))))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.83/1.03  thf('3', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.83/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.83/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.83/1.03  thf('4', plain,
% 0.83/1.03      ((m1_subset_1 @ 
% 0.83/1.03        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.83/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['0', '3'])).
% 0.83/1.03  thf('5', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('6', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(redefinition_k4_relset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.83/1.03     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.83/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.83/1.03       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.83/1.03  thf('7', plain,
% 0.83/1.03      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.83/1.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.83/1.03          | ((k4_relset_1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 0.83/1.03              = (k5_relat_1 @ X20 @ X23)))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.83/1.03  thf('8', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.83/1.03            = (k5_relat_1 @ sk_D @ X0))
% 0.83/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.03  thf('9', plain,
% 0.83/1.03      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.83/1.03         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.83/1.03      inference('sup-', [status(thm)], ['5', '8'])).
% 0.83/1.03  thf('10', plain,
% 0.83/1.03      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.83/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.83/1.03      inference('demod', [status(thm)], ['4', '9'])).
% 0.83/1.03  thf(redefinition_k2_relset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.83/1.03  thf('11', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.03         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.83/1.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.03  thf('12', plain,
% 0.83/1.03      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 0.83/1.03         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.03  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(d1_funct_2, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.83/1.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.83/1.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.83/1.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.83/1.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.83/1.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.83/1.03  thf(zf_stmt_1, axiom,
% 0.83/1.03    (![C:$i,B:$i,A:$i]:
% 0.83/1.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.83/1.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.83/1.03  thf('14', plain,
% 0.83/1.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.83/1.03         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.83/1.03          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.83/1.03          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.83/1.03  thf('15', plain,
% 0.83/1.03      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 0.83/1.03        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['13', '14'])).
% 0.83/1.03  thf(zf_stmt_2, axiom,
% 0.83/1.03    (![B:$i,A:$i]:
% 0.83/1.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.83/1.03       ( zip_tseitin_0 @ B @ A ) ))).
% 0.83/1.03  thf('16', plain,
% 0.83/1.03      (![X26 : $i, X27 : $i]:
% 0.83/1.03         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.83/1.03  thf('17', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.83/1.03  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.83/1.03  thf(zf_stmt_5, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.83/1.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.83/1.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.83/1.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.83/1.03  thf('18', plain,
% 0.83/1.03      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.83/1.03         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.83/1.03          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.83/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.83/1.03  thf('19', plain,
% 0.83/1.03      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.83/1.03      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.03  thf('20', plain,
% 0.83/1.03      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 0.83/1.03      inference('sup-', [status(thm)], ['16', '19'])).
% 0.83/1.03  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('22', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 0.83/1.03      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.83/1.03  thf('23', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(redefinition_k1_relset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.83/1.03  thf('24', plain,
% 0.83/1.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.03         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.83/1.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.83/1.03  thf('25', plain,
% 0.83/1.03      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.83/1.03      inference('sup-', [status(thm)], ['23', '24'])).
% 0.83/1.03  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 0.83/1.03      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.83/1.03  thf('27', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('28', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.03         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.83/1.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.03  thf('29', plain,
% 0.83/1.03      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.83/1.03      inference('sup-', [status(thm)], ['27', '28'])).
% 0.83/1.03  thf('30', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.83/1.03      inference('sup+', [status(thm)], ['29', '30'])).
% 0.83/1.03  thf(t47_relat_1, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( v1_relat_1 @ A ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( v1_relat_1 @ B ) =>
% 0.83/1.03           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.83/1.03             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.83/1.03  thf('32', plain,
% 0.83/1.03      (![X3 : $i, X4 : $i]:
% 0.83/1.03         (~ (v1_relat_1 @ X3)
% 0.83/1.03          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X4)) = (k2_relat_1 @ X4))
% 0.83/1.03          | ~ (r1_tarski @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X3))
% 0.83/1.03          | ~ (v1_relat_1 @ X4))),
% 0.83/1.03      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.83/1.03  thf('33', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 0.83/1.03          | ~ (v1_relat_1 @ X0)
% 0.83/1.03          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 0.83/1.03          | ~ (v1_relat_1 @ sk_D))),
% 0.83/1.03      inference('sup-', [status(thm)], ['31', '32'])).
% 0.83/1.03  thf('34', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(cc1_relset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.03       ( v1_relat_1 @ C ) ))).
% 0.83/1.03  thf('35', plain,
% 0.83/1.03      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.03         ((v1_relat_1 @ X5)
% 0.83/1.03          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.83/1.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.03  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.03  thf('37', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 0.83/1.03          | ~ (v1_relat_1 @ X0)
% 0.83/1.03          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 0.83/1.03      inference('demod', [status(thm)], ['33', '36'])).
% 0.83/1.03  thf('38', plain,
% 0.83/1.03      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.83/1.03        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 0.83/1.03        | ~ (v1_relat_1 @ sk_E))),
% 0.83/1.03      inference('sup-', [status(thm)], ['26', '37'])).
% 0.83/1.03  thf(d10_xboole_0, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.03  thf('39', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.83/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.03  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.03      inference('simplify', [status(thm)], ['39'])).
% 0.83/1.03  thf('41', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('42', plain,
% 0.83/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.03         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.83/1.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.03  thf('43', plain,
% 0.83/1.03      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 0.83/1.03      inference('sup-', [status(thm)], ['41', '42'])).
% 0.83/1.03  thf('44', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('45', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.83/1.03      inference('sup+', [status(thm)], ['43', '44'])).
% 0.83/1.03  thf('46', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('47', plain,
% 0.83/1.03      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.03         ((v1_relat_1 @ X5)
% 0.83/1.03          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.83/1.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.03  thf('48', plain, ((v1_relat_1 @ sk_E)),
% 0.83/1.03      inference('sup-', [status(thm)], ['46', '47'])).
% 0.83/1.03  thf('49', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.83/1.03      inference('demod', [status(thm)], ['38', '40', '45', '48'])).
% 0.83/1.03  thf('50', plain,
% 0.83/1.03      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.83/1.03      inference('demod', [status(thm)], ['12', '49'])).
% 0.83/1.03  thf('51', plain,
% 0.83/1.03      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.83/1.03         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('52', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('53', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(redefinition_k1_partfun1, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.83/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.83/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.83/1.03         ( v1_funct_1 @ F ) & 
% 0.83/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.83/1.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.83/1.03  thf('54', plain,
% 0.83/1.03      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.83/1.03          | ~ (v1_funct_1 @ X34)
% 0.83/1.03          | ~ (v1_funct_1 @ X37)
% 0.83/1.03          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.83/1.03          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 0.83/1.03              = (k5_relat_1 @ X34 @ X37)))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.83/1.03  thf('55', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.83/1.03            = (k5_relat_1 @ sk_D @ X0))
% 0.83/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.83/1.03          | ~ (v1_funct_1 @ X0)
% 0.83/1.03          | ~ (v1_funct_1 @ sk_D))),
% 0.83/1.03      inference('sup-', [status(thm)], ['53', '54'])).
% 0.83/1.03  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('57', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.83/1.03            = (k5_relat_1 @ sk_D @ X0))
% 0.83/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.83/1.03          | ~ (v1_funct_1 @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['55', '56'])).
% 0.83/1.03  thf('58', plain,
% 0.83/1.03      ((~ (v1_funct_1 @ sk_E)
% 0.83/1.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.83/1.03            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['52', '57'])).
% 0.83/1.03  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('60', plain,
% 0.83/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.83/1.03         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.83/1.03      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.03  thf('61', plain,
% 0.83/1.03      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 0.83/1.03      inference('demod', [status(thm)], ['51', '60'])).
% 0.83/1.03  thf('62', plain, ($false),
% 0.83/1.03      inference('simplify_reflect-', [status(thm)], ['50', '61'])).
% 0.83/1.03  
% 0.83/1.03  % SZS output end Refutation
% 0.83/1.03  
% 0.83/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
