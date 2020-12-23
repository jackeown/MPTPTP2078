%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Ec8XBNzZv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:54 EST 2020

% Result     : Theorem 13.23s
% Output     : Refutation 13.23s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 455 expanded)
%              Number of leaves         :   45 ( 153 expanded)
%              Depth                    :   19
%              Number of atoms          : 1293 (8979 expanded)
%              Number of equality atoms :   65 ( 520 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k4_relset_1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
       != ( k2_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('39',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['49','56','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('63',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','44','45','46','60','61','62'])).

thf('64',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['49','56','59'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_E ) ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['64','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('74',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v5_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('85',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ ( k2_relat_1 @ sk_E ) @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf('90',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('92',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['42','43'])).

thf('96',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_C
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['88','89','96','97'])).

thf('99',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['63','98'])).

thf('100',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','100'])).

thf('102',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Ec8XBNzZv
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.23/13.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.23/13.45  % Solved by: fo/fo7.sh
% 13.23/13.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.23/13.45  % done 4375 iterations in 12.992s
% 13.23/13.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.23/13.45  % SZS output start Refutation
% 13.23/13.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 13.23/13.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.23/13.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.23/13.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 13.23/13.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 13.23/13.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.23/13.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.23/13.45  thf(sk_E_type, type, sk_E: $i).
% 13.23/13.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 13.23/13.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 13.23/13.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 13.23/13.45  thf(sk_D_type, type, sk_D: $i).
% 13.23/13.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.23/13.45  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 13.23/13.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 13.23/13.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.23/13.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.23/13.45  thf(sk_B_type, type, sk_B: $i).
% 13.23/13.45  thf(sk_C_type, type, sk_C: $i).
% 13.23/13.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.23/13.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 13.23/13.45  thf(sk_A_type, type, sk_A: $i).
% 13.23/13.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 13.23/13.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 13.23/13.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 13.23/13.45  thf(t28_funct_2, conjecture,
% 13.23/13.45    (![A:$i,B:$i,C:$i,D:$i]:
% 13.23/13.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 13.23/13.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.23/13.45       ( ![E:$i]:
% 13.23/13.45         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 13.23/13.45             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 13.23/13.45           ( ( ( ( k2_relset_1 @
% 13.23/13.45                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 13.23/13.45                 ( C ) ) & 
% 13.23/13.45               ( v2_funct_1 @ E ) ) =>
% 13.23/13.45             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 13.23/13.45               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 13.23/13.45  thf(zf_stmt_0, negated_conjecture,
% 13.23/13.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 13.23/13.45        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 13.23/13.45            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.23/13.45          ( ![E:$i]:
% 13.23/13.45            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 13.23/13.45                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 13.23/13.45              ( ( ( ( k2_relset_1 @
% 13.23/13.45                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 13.23/13.45                    ( C ) ) & 
% 13.23/13.45                  ( v2_funct_1 @ E ) ) =>
% 13.23/13.45                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 13.23/13.45                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 13.23/13.45    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 13.23/13.45  thf('0', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf(cc2_relset_1, axiom,
% 13.23/13.45    (![A:$i,B:$i,C:$i]:
% 13.23/13.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.23/13.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 13.23/13.45  thf('1', plain,
% 13.23/13.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.23/13.45         ((v5_relat_1 @ X14 @ X16)
% 13.23/13.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 13.23/13.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.23/13.45  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 13.23/13.45      inference('sup-', [status(thm)], ['0', '1'])).
% 13.23/13.45  thf(d19_relat_1, axiom,
% 13.23/13.45    (![A:$i,B:$i]:
% 13.23/13.45     ( ( v1_relat_1 @ B ) =>
% 13.23/13.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 13.23/13.45  thf('3', plain,
% 13.23/13.45      (![X5 : $i, X6 : $i]:
% 13.23/13.45         (~ (v5_relat_1 @ X5 @ X6)
% 13.23/13.45          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 13.23/13.45          | ~ (v1_relat_1 @ X5))),
% 13.23/13.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.23/13.45  thf('4', plain,
% 13.23/13.45      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 13.23/13.45      inference('sup-', [status(thm)], ['2', '3'])).
% 13.23/13.45  thf('5', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf(cc2_relat_1, axiom,
% 13.23/13.45    (![A:$i]:
% 13.23/13.45     ( ( v1_relat_1 @ A ) =>
% 13.23/13.45       ( ![B:$i]:
% 13.23/13.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 13.23/13.45  thf('6', plain,
% 13.23/13.45      (![X3 : $i, X4 : $i]:
% 13.23/13.45         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 13.23/13.45          | (v1_relat_1 @ X3)
% 13.23/13.45          | ~ (v1_relat_1 @ X4))),
% 13.23/13.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.23/13.45  thf('7', plain,
% 13.23/13.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 13.23/13.45      inference('sup-', [status(thm)], ['5', '6'])).
% 13.23/13.45  thf(fc6_relat_1, axiom,
% 13.23/13.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 13.23/13.45  thf('8', plain,
% 13.23/13.45      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 13.23/13.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.23/13.45  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 13.23/13.45      inference('demod', [status(thm)], ['7', '8'])).
% 13.23/13.45  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 13.23/13.45      inference('demod', [status(thm)], ['4', '9'])).
% 13.23/13.45  thf(d10_xboole_0, axiom,
% 13.23/13.45    (![A:$i,B:$i]:
% 13.23/13.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.23/13.45  thf('11', plain,
% 13.23/13.45      (![X0 : $i, X2 : $i]:
% 13.23/13.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 13.23/13.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.23/13.45  thf('12', plain,
% 13.23/13.45      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 13.23/13.45        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 13.23/13.45      inference('sup-', [status(thm)], ['10', '11'])).
% 13.23/13.45  thf('13', plain,
% 13.23/13.45      (((k2_relset_1 @ sk_A @ sk_C @ 
% 13.23/13.45         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('14', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('15', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf(redefinition_k1_partfun1, axiom,
% 13.23/13.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.23/13.45     ( ( ( v1_funct_1 @ E ) & 
% 13.23/13.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.23/13.45         ( v1_funct_1 @ F ) & 
% 13.23/13.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.23/13.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 13.23/13.45  thf('16', plain,
% 13.23/13.45      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 13.23/13.45         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 13.23/13.45          | ~ (v1_funct_1 @ X43)
% 13.23/13.45          | ~ (v1_funct_1 @ X46)
% 13.23/13.45          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 13.23/13.45          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 13.23/13.45              = (k5_relat_1 @ X43 @ X46)))),
% 13.23/13.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 13.23/13.45  thf('17', plain,
% 13.23/13.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.23/13.45         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 13.23/13.45            = (k5_relat_1 @ sk_D @ X0))
% 13.23/13.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 13.23/13.45          | ~ (v1_funct_1 @ X0)
% 13.23/13.45          | ~ (v1_funct_1 @ sk_D))),
% 13.23/13.45      inference('sup-', [status(thm)], ['15', '16'])).
% 13.23/13.45  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('19', plain,
% 13.23/13.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.23/13.45         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 13.23/13.45            = (k5_relat_1 @ sk_D @ X0))
% 13.23/13.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 13.23/13.45          | ~ (v1_funct_1 @ X0))),
% 13.23/13.45      inference('demod', [status(thm)], ['17', '18'])).
% 13.23/13.45  thf('20', plain,
% 13.23/13.45      ((~ (v1_funct_1 @ sk_E)
% 13.23/13.45        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 13.23/13.45            = (k5_relat_1 @ sk_D @ sk_E)))),
% 13.23/13.45      inference('sup-', [status(thm)], ['14', '19'])).
% 13.23/13.45  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('22', plain,
% 13.23/13.45      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 13.23/13.45         = (k5_relat_1 @ sk_D @ sk_E))),
% 13.23/13.45      inference('demod', [status(thm)], ['20', '21'])).
% 13.23/13.45  thf('23', plain,
% 13.23/13.45      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 13.23/13.45      inference('demod', [status(thm)], ['13', '22'])).
% 13.23/13.45  thf('24', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('25', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf(dt_k4_relset_1, axiom,
% 13.23/13.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.23/13.45     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.23/13.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.23/13.45       ( m1_subset_1 @
% 13.23/13.45         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 13.23/13.45         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 13.23/13.45  thf('26', plain,
% 13.23/13.45      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 13.23/13.45         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.23/13.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 13.23/13.45          | (m1_subset_1 @ (k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 13.23/13.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 13.23/13.45      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 13.23/13.45  thf('27', plain,
% 13.23/13.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.23/13.45         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 13.23/13.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 13.23/13.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 13.23/13.45      inference('sup-', [status(thm)], ['25', '26'])).
% 13.23/13.45  thf('28', plain,
% 13.23/13.45      ((m1_subset_1 @ 
% 13.23/13.45        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 13.23/13.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 13.23/13.45      inference('sup-', [status(thm)], ['24', '27'])).
% 13.23/13.45  thf('29', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('30', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf(redefinition_k4_relset_1, axiom,
% 13.23/13.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.23/13.45     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.23/13.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.23/13.45       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 13.23/13.45  thf('31', plain,
% 13.23/13.45      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 13.23/13.45         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 13.23/13.45          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 13.23/13.45          | ((k4_relset_1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 13.23/13.45              = (k5_relat_1 @ X29 @ X32)))),
% 13.23/13.45      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 13.23/13.45  thf('32', plain,
% 13.23/13.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.23/13.45         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 13.23/13.45            = (k5_relat_1 @ sk_D @ X0))
% 13.23/13.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 13.23/13.45      inference('sup-', [status(thm)], ['30', '31'])).
% 13.23/13.45  thf('33', plain,
% 13.23/13.45      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 13.23/13.45         = (k5_relat_1 @ sk_D @ sk_E))),
% 13.23/13.45      inference('sup-', [status(thm)], ['29', '32'])).
% 13.23/13.45  thf('34', plain,
% 13.23/13.45      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 13.23/13.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 13.23/13.45      inference('demod', [status(thm)], ['28', '33'])).
% 13.23/13.45  thf(redefinition_k2_relset_1, axiom,
% 13.23/13.45    (![A:$i,B:$i,C:$i]:
% 13.23/13.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.23/13.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 13.23/13.45  thf('35', plain,
% 13.23/13.45      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.23/13.45         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 13.23/13.45          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 13.23/13.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.23/13.45  thf('36', plain,
% 13.23/13.45      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 13.23/13.45         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 13.23/13.45      inference('sup-', [status(thm)], ['34', '35'])).
% 13.23/13.45  thf('37', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 13.23/13.45      inference('sup+', [status(thm)], ['23', '36'])).
% 13.23/13.45  thf(t51_funct_1, axiom,
% 13.23/13.45    (![A:$i]:
% 13.23/13.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.23/13.45       ( ![B:$i]:
% 13.23/13.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.23/13.45           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 13.23/13.45               ( v2_funct_1 @ A ) ) =>
% 13.23/13.45             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 13.23/13.45  thf('38', plain,
% 13.23/13.45      (![X9 : $i, X10 : $i]:
% 13.23/13.45         (~ (v1_relat_1 @ X9)
% 13.23/13.45          | ~ (v1_funct_1 @ X9)
% 13.23/13.45          | (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 13.23/13.45          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) != (k2_relat_1 @ X10))
% 13.23/13.45          | ~ (v2_funct_1 @ X10)
% 13.23/13.45          | ~ (v1_funct_1 @ X10)
% 13.23/13.45          | ~ (v1_relat_1 @ X10))),
% 13.23/13.45      inference('cnf', [status(esa)], [t51_funct_1])).
% 13.23/13.45  thf('39', plain,
% 13.23/13.45      ((((sk_C) != (k2_relat_1 @ sk_E))
% 13.23/13.45        | ~ (v1_relat_1 @ sk_E)
% 13.23/13.45        | ~ (v1_funct_1 @ sk_E)
% 13.23/13.45        | ~ (v2_funct_1 @ sk_E)
% 13.23/13.45        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 13.23/13.45        | ~ (v1_funct_1 @ sk_D)
% 13.23/13.45        | ~ (v1_relat_1 @ sk_D))),
% 13.23/13.45      inference('sup-', [status(thm)], ['37', '38'])).
% 13.23/13.45  thf('40', plain,
% 13.23/13.45      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('41', plain,
% 13.23/13.45      (![X3 : $i, X4 : $i]:
% 13.23/13.45         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 13.23/13.45          | (v1_relat_1 @ X3)
% 13.23/13.45          | ~ (v1_relat_1 @ X4))),
% 13.23/13.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.23/13.45  thf('42', plain,
% 13.23/13.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 13.23/13.45      inference('sup-', [status(thm)], ['40', '41'])).
% 13.23/13.45  thf('43', plain,
% 13.23/13.45      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 13.23/13.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.23/13.45  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 13.23/13.45      inference('demod', [status(thm)], ['42', '43'])).
% 13.23/13.45  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('46', plain, ((v2_funct_1 @ sk_E)),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf('47', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 13.23/13.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.45  thf(d1_funct_2, axiom,
% 13.23/13.45    (![A:$i,B:$i,C:$i]:
% 13.23/13.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.23/13.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.23/13.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 13.23/13.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 13.23/13.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.23/13.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 13.23/13.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 13.23/13.46  thf(zf_stmt_1, axiom,
% 13.23/13.46    (![C:$i,B:$i,A:$i]:
% 13.23/13.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 13.23/13.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 13.23/13.46  thf('48', plain,
% 13.23/13.46      (![X37 : $i, X38 : $i, X39 : $i]:
% 13.23/13.46         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 13.23/13.46          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 13.23/13.46          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.23/13.46  thf('49', plain,
% 13.23/13.46      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 13.23/13.46        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 13.23/13.46      inference('sup-', [status(thm)], ['47', '48'])).
% 13.23/13.46  thf(zf_stmt_2, axiom,
% 13.23/13.46    (![B:$i,A:$i]:
% 13.23/13.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.23/13.46       ( zip_tseitin_0 @ B @ A ) ))).
% 13.23/13.46  thf('50', plain,
% 13.23/13.46      (![X35 : $i, X36 : $i]:
% 13.23/13.46         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 13.23/13.46  thf('51', plain,
% 13.23/13.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 13.23/13.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 13.23/13.46  thf(zf_stmt_5, axiom,
% 13.23/13.46    (![A:$i,B:$i,C:$i]:
% 13.23/13.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.23/13.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 13.23/13.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.23/13.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 13.23/13.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 13.23/13.46  thf('52', plain,
% 13.23/13.46      (![X40 : $i, X41 : $i, X42 : $i]:
% 13.23/13.46         (~ (zip_tseitin_0 @ X40 @ X41)
% 13.23/13.46          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 13.23/13.46          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.23/13.46  thf('53', plain,
% 13.23/13.46      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 13.23/13.46      inference('sup-', [status(thm)], ['51', '52'])).
% 13.23/13.46  thf('54', plain,
% 13.23/13.46      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 13.23/13.46      inference('sup-', [status(thm)], ['50', '53'])).
% 13.23/13.46  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf('56', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 13.23/13.46      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 13.23/13.46  thf('57', plain,
% 13.23/13.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf(redefinition_k1_relset_1, axiom,
% 13.23/13.46    (![A:$i,B:$i,C:$i]:
% 13.23/13.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.23/13.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 13.23/13.46  thf('58', plain,
% 13.23/13.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 13.23/13.46         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 13.23/13.46          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 13.23/13.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.23/13.46  thf('59', plain,
% 13.23/13.46      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 13.23/13.46      inference('sup-', [status(thm)], ['57', '58'])).
% 13.23/13.46  thf('60', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 13.23/13.46      inference('demod', [status(thm)], ['49', '56', '59'])).
% 13.23/13.46  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 13.23/13.46      inference('demod', [status(thm)], ['7', '8'])).
% 13.23/13.46  thf('63', plain,
% 13.23/13.46      ((((sk_C) != (k2_relat_1 @ sk_E))
% 13.23/13.46        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 13.23/13.46      inference('demod', [status(thm)],
% 13.23/13.46                ['39', '44', '45', '46', '60', '61', '62'])).
% 13.23/13.46  thf('64', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 13.23/13.46      inference('demod', [status(thm)], ['49', '56', '59'])).
% 13.23/13.46  thf('65', plain,
% 13.23/13.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 13.23/13.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.23/13.46  thf('66', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 13.23/13.46      inference('simplify', [status(thm)], ['65'])).
% 13.23/13.46  thf(t4_funct_2, axiom,
% 13.23/13.46    (![A:$i,B:$i]:
% 13.23/13.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.23/13.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 13.23/13.46         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 13.23/13.46           ( m1_subset_1 @
% 13.23/13.46             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 13.23/13.46  thf('67', plain,
% 13.23/13.46      (![X49 : $i, X50 : $i]:
% 13.23/13.46         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 13.23/13.46          | (m1_subset_1 @ X49 @ 
% 13.23/13.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ X50)))
% 13.23/13.46          | ~ (v1_funct_1 @ X49)
% 13.23/13.46          | ~ (v1_relat_1 @ X49))),
% 13.23/13.46      inference('cnf', [status(esa)], [t4_funct_2])).
% 13.23/13.46  thf('68', plain,
% 13.23/13.46      (![X0 : $i]:
% 13.23/13.46         (~ (v1_relat_1 @ X0)
% 13.23/13.46          | ~ (v1_funct_1 @ X0)
% 13.23/13.46          | (m1_subset_1 @ X0 @ 
% 13.23/13.46             (k1_zfmisc_1 @ 
% 13.23/13.46              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 13.23/13.46      inference('sup-', [status(thm)], ['66', '67'])).
% 13.23/13.46  thf('69', plain,
% 13.23/13.46      (((m1_subset_1 @ sk_E @ 
% 13.23/13.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_E))))
% 13.23/13.46        | ~ (v1_funct_1 @ sk_E)
% 13.23/13.46        | ~ (v1_relat_1 @ sk_E))),
% 13.23/13.46      inference('sup+', [status(thm)], ['64', '68'])).
% 13.23/13.46  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 13.23/13.46      inference('demod', [status(thm)], ['42', '43'])).
% 13.23/13.46  thf('72', plain,
% 13.23/13.46      ((m1_subset_1 @ sk_E @ 
% 13.23/13.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_E))))),
% 13.23/13.46      inference('demod', [status(thm)], ['69', '70', '71'])).
% 13.23/13.46  thf('73', plain,
% 13.23/13.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.23/13.46         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 13.23/13.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 13.23/13.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 13.23/13.46      inference('sup-', [status(thm)], ['25', '26'])).
% 13.23/13.46  thf('74', plain,
% 13.23/13.46      ((m1_subset_1 @ 
% 13.23/13.46        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E) @ 
% 13.23/13.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_E))))),
% 13.23/13.46      inference('sup-', [status(thm)], ['72', '73'])).
% 13.23/13.46  thf('75', plain,
% 13.23/13.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.23/13.46         ((v5_relat_1 @ X14 @ X16)
% 13.23/13.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 13.23/13.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.23/13.46  thf('76', plain,
% 13.23/13.46      ((v5_relat_1 @ 
% 13.23/13.46        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E) @ 
% 13.23/13.46        (k2_relat_1 @ sk_E))),
% 13.23/13.46      inference('sup-', [status(thm)], ['74', '75'])).
% 13.23/13.46  thf('77', plain,
% 13.23/13.46      (![X5 : $i, X6 : $i]:
% 13.23/13.46         (~ (v5_relat_1 @ X5 @ X6)
% 13.23/13.46          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 13.23/13.46          | ~ (v1_relat_1 @ X5))),
% 13.23/13.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.23/13.46  thf('78', plain,
% 13.23/13.46      ((~ (v1_relat_1 @ 
% 13.23/13.46           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ 
% 13.23/13.46            sk_E))
% 13.23/13.46        | (r1_tarski @ 
% 13.23/13.46           (k2_relat_1 @ 
% 13.23/13.46            (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ 
% 13.23/13.46             sk_E)) @ 
% 13.23/13.46           (k2_relat_1 @ sk_E)))),
% 13.23/13.46      inference('sup-', [status(thm)], ['76', '77'])).
% 13.23/13.46  thf('79', plain,
% 13.23/13.46      ((m1_subset_1 @ 
% 13.23/13.46        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E) @ 
% 13.23/13.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_E))))),
% 13.23/13.46      inference('sup-', [status(thm)], ['72', '73'])).
% 13.23/13.46  thf(cc1_relset_1, axiom,
% 13.23/13.46    (![A:$i,B:$i,C:$i]:
% 13.23/13.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.23/13.46       ( v1_relat_1 @ C ) ))).
% 13.23/13.46  thf('80', plain,
% 13.23/13.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 13.23/13.46         ((v1_relat_1 @ X11)
% 13.23/13.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 13.23/13.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.23/13.46  thf('81', plain,
% 13.23/13.46      ((v1_relat_1 @ 
% 13.23/13.46        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E))),
% 13.23/13.46      inference('sup-', [status(thm)], ['79', '80'])).
% 13.23/13.46  thf('82', plain,
% 13.23/13.46      ((r1_tarski @ 
% 13.23/13.46        (k2_relat_1 @ 
% 13.23/13.46         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E)) @ 
% 13.23/13.46        (k2_relat_1 @ sk_E))),
% 13.23/13.46      inference('demod', [status(thm)], ['78', '81'])).
% 13.23/13.46  thf('83', plain,
% 13.23/13.46      ((m1_subset_1 @ sk_E @ 
% 13.23/13.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_E))))),
% 13.23/13.46      inference('demod', [status(thm)], ['69', '70', '71'])).
% 13.23/13.46  thf('84', plain,
% 13.23/13.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.23/13.46         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 13.23/13.46            = (k5_relat_1 @ sk_D @ X0))
% 13.23/13.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 13.23/13.46      inference('sup-', [status(thm)], ['30', '31'])).
% 13.23/13.46  thf('85', plain,
% 13.23/13.46      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ (k2_relat_1 @ sk_E) @ sk_D @ sk_E)
% 13.23/13.46         = (k5_relat_1 @ sk_D @ sk_E))),
% 13.23/13.46      inference('sup-', [status(thm)], ['83', '84'])).
% 13.23/13.46  thf('86', plain,
% 13.23/13.46      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) @ 
% 13.23/13.46        (k2_relat_1 @ sk_E))),
% 13.23/13.46      inference('demod', [status(thm)], ['82', '85'])).
% 13.23/13.46  thf('87', plain,
% 13.23/13.46      (![X0 : $i, X2 : $i]:
% 13.23/13.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 13.23/13.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.23/13.46  thf('88', plain,
% 13.23/13.46      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ 
% 13.23/13.46           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 13.23/13.46        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))))),
% 13.23/13.46      inference('sup-', [status(thm)], ['86', '87'])).
% 13.23/13.46  thf('89', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 13.23/13.46      inference('sup+', [status(thm)], ['23', '36'])).
% 13.23/13.46  thf('90', plain,
% 13.23/13.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf('91', plain,
% 13.23/13.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.23/13.46         ((v5_relat_1 @ X14 @ X16)
% 13.23/13.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 13.23/13.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.23/13.46  thf('92', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 13.23/13.46      inference('sup-', [status(thm)], ['90', '91'])).
% 13.23/13.46  thf('93', plain,
% 13.23/13.46      (![X5 : $i, X6 : $i]:
% 13.23/13.46         (~ (v5_relat_1 @ X5 @ X6)
% 13.23/13.46          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 13.23/13.46          | ~ (v1_relat_1 @ X5))),
% 13.23/13.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.23/13.46  thf('94', plain,
% 13.23/13.46      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 13.23/13.46      inference('sup-', [status(thm)], ['92', '93'])).
% 13.23/13.46  thf('95', plain, ((v1_relat_1 @ sk_E)),
% 13.23/13.46      inference('demod', [status(thm)], ['42', '43'])).
% 13.23/13.46  thf('96', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 13.23/13.46      inference('demod', [status(thm)], ['94', '95'])).
% 13.23/13.46  thf('97', plain, (((sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 13.23/13.46      inference('sup+', [status(thm)], ['23', '36'])).
% 13.23/13.46  thf('98', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 13.23/13.46      inference('demod', [status(thm)], ['88', '89', '96', '97'])).
% 13.23/13.46  thf('99', plain,
% 13.23/13.46      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 13.23/13.46      inference('demod', [status(thm)], ['63', '98'])).
% 13.23/13.46  thf('100', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 13.23/13.46      inference('simplify', [status(thm)], ['99'])).
% 13.23/13.46  thf('101', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 13.23/13.46      inference('demod', [status(thm)], ['12', '100'])).
% 13.23/13.46  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf('103', plain,
% 13.23/13.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.23/13.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.23/13.46  thf('104', plain,
% 13.23/13.46      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.23/13.46         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 13.23/13.46          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 13.23/13.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.23/13.46  thf('105', plain,
% 13.23/13.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 13.23/13.46      inference('sup-', [status(thm)], ['103', '104'])).
% 13.23/13.46  thf('106', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 13.23/13.46      inference('demod', [status(thm)], ['102', '105'])).
% 13.23/13.46  thf('107', plain, ($false),
% 13.23/13.46      inference('simplify_reflect-', [status(thm)], ['101', '106'])).
% 13.23/13.46  
% 13.23/13.46  % SZS output end Refutation
% 13.23/13.46  
% 13.23/13.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
