%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZI6spnKR9V

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:02 EST 2020

% Result     : Theorem 26.03s
% Output     : Refutation 26.03s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 356 expanded)
%              Number of leaves         :   54 ( 125 expanded)
%              Depth                    :   19
%              Number of atoms          : 1458 (6511 expanded)
%              Number of equality atoms :   55 (  84 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('13',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('23',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('24',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['32','35'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('48',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v2_funct_1 @ X11 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','72','73'])).

thf('75',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( v2_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','80'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('82',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('83',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','87'])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('91',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( r2_relset_1 @ X54 @ X54 @ ( k1_partfun1 @ X54 @ X55 @ X55 @ X54 @ X53 @ X56 ) @ ( k6_partfun1 @ X54 ) )
      | ( ( k2_relset_1 @ X55 @ X54 @ X56 )
        = X54 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','95'])).

thf('97',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('98',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('99',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['96','100','103','104','105','106'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('108',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ X39 )
       != X38 )
      | ( v2_funct_2 @ X39 @ X38 )
      | ~ ( v5_relat_1 @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('109',plain,(
    ! [X39: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v5_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
      | ( v2_funct_2 @ X39 @ ( k2_relat_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['96','100','103','104','105','106'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('116',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['110','113','114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['88','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZI6spnKR9V
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 26.03/26.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.03/26.28  % Solved by: fo/fo7.sh
% 26.03/26.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.03/26.28  % done 14137 iterations in 25.817s
% 26.03/26.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.03/26.28  % SZS output start Refutation
% 26.03/26.28  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 26.03/26.28  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 26.03/26.28  thf(sk_D_type, type, sk_D: $i).
% 26.03/26.28  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 26.03/26.28  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 26.03/26.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 26.03/26.28  thf(sk_C_type, type, sk_C: $i).
% 26.03/26.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.03/26.28  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 26.03/26.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.03/26.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 26.03/26.28  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 26.03/26.28  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 26.03/26.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.03/26.28  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 26.03/26.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 26.03/26.28  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 26.03/26.28  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 26.03/26.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.03/26.28  thf(sk_A_type, type, sk_A: $i).
% 26.03/26.28  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 26.03/26.28  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 26.03/26.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 26.03/26.28  thf(sk_B_type, type, sk_B: $i).
% 26.03/26.28  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 26.03/26.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 26.03/26.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 26.03/26.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 26.03/26.28  thf(t29_funct_2, conjecture,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 26.03/26.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.03/26.28       ( ![D:$i]:
% 26.03/26.28         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 26.03/26.28             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 26.03/26.28           ( ( r2_relset_1 @
% 26.03/26.28               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 26.03/26.28               ( k6_partfun1 @ A ) ) =>
% 26.03/26.28             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 26.03/26.28  thf(zf_stmt_0, negated_conjecture,
% 26.03/26.28    (~( ![A:$i,B:$i,C:$i]:
% 26.03/26.28        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 26.03/26.28            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.03/26.28          ( ![D:$i]:
% 26.03/26.28            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 26.03/26.28                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 26.03/26.28              ( ( r2_relset_1 @
% 26.03/26.28                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 26.03/26.28                  ( k6_partfun1 @ A ) ) =>
% 26.03/26.28                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 26.03/26.28    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 26.03/26.28  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('1', plain,
% 26.03/26.28      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 26.03/26.28      inference('split', [status(esa)], ['0'])).
% 26.03/26.28  thf('2', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('3', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(redefinition_k1_partfun1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 26.03/26.28     ( ( ( v1_funct_1 @ E ) & 
% 26.03/26.28         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.03/26.28         ( v1_funct_1 @ F ) & 
% 26.03/26.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 26.03/26.28       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 26.03/26.28  thf('4', plain,
% 26.03/26.28      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 26.03/26.28         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 26.03/26.28          | ~ (v1_funct_1 @ X46)
% 26.03/26.28          | ~ (v1_funct_1 @ X49)
% 26.03/26.28          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 26.03/26.28          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 26.03/26.28              = (k5_relat_1 @ X46 @ X49)))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 26.03/26.28  thf('5', plain,
% 26.03/26.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.03/26.28         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 26.03/26.28            = (k5_relat_1 @ sk_C @ X0))
% 26.03/26.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 26.03/26.28          | ~ (v1_funct_1 @ X0)
% 26.03/26.28          | ~ (v1_funct_1 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['3', '4'])).
% 26.03/26.28  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('7', plain,
% 26.03/26.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.03/26.28         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 26.03/26.28            = (k5_relat_1 @ sk_C @ X0))
% 26.03/26.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 26.03/26.28          | ~ (v1_funct_1 @ X0))),
% 26.03/26.28      inference('demod', [status(thm)], ['5', '6'])).
% 26.03/26.28  thf('8', plain,
% 26.03/26.28      ((~ (v1_funct_1 @ sk_D)
% 26.03/26.28        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 26.03/26.28            = (k5_relat_1 @ sk_C @ sk_D)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['2', '7'])).
% 26.03/26.28  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('10', plain,
% 26.03/26.28      ((r2_relset_1 @ sk_A @ sk_A @ 
% 26.03/26.28        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 26.03/26.28        (k6_partfun1 @ sk_A))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('11', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('12', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(dt_k1_partfun1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 26.03/26.28     ( ( ( v1_funct_1 @ E ) & 
% 26.03/26.28         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.03/26.28         ( v1_funct_1 @ F ) & 
% 26.03/26.28         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 26.03/26.28       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 26.03/26.28         ( m1_subset_1 @
% 26.03/26.28           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 26.03/26.28           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 26.03/26.28  thf('13', plain,
% 26.03/26.28      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 26.03/26.28         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 26.03/26.28          | ~ (v1_funct_1 @ X40)
% 26.03/26.28          | ~ (v1_funct_1 @ X43)
% 26.03/26.28          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 26.03/26.28          | (m1_subset_1 @ (k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43) @ 
% 26.03/26.28             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X45))))),
% 26.03/26.28      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 26.03/26.28  thf('14', plain,
% 26.03/26.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.03/26.28         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 26.03/26.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 26.03/26.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 26.03/26.28          | ~ (v1_funct_1 @ X1)
% 26.03/26.28          | ~ (v1_funct_1 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['12', '13'])).
% 26.03/26.28  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('16', plain,
% 26.03/26.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.03/26.28         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 26.03/26.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 26.03/26.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 26.03/26.28          | ~ (v1_funct_1 @ X1))),
% 26.03/26.28      inference('demod', [status(thm)], ['14', '15'])).
% 26.03/26.28  thf('17', plain,
% 26.03/26.28      ((~ (v1_funct_1 @ sk_D)
% 26.03/26.28        | (m1_subset_1 @ 
% 26.03/26.28           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 26.03/26.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 26.03/26.28      inference('sup-', [status(thm)], ['11', '16'])).
% 26.03/26.28  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('19', plain,
% 26.03/26.28      ((m1_subset_1 @ 
% 26.03/26.28        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 26.03/26.28        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.03/26.28      inference('demod', [status(thm)], ['17', '18'])).
% 26.03/26.28  thf(redefinition_r2_relset_1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i,D:$i]:
% 26.03/26.28     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.03/26.28         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.03/26.28       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 26.03/26.28  thf('20', plain,
% 26.03/26.28      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 26.03/26.28         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 26.03/26.28          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 26.03/26.28          | ((X25) = (X28))
% 26.03/26.28          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 26.03/26.28  thf('21', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.03/26.28             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 26.03/26.28          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 26.03/26.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 26.03/26.28      inference('sup-', [status(thm)], ['19', '20'])).
% 26.03/26.28  thf('22', plain,
% 26.03/26.28      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 26.03/26.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 26.03/26.28        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 26.03/26.28            = (k6_partfun1 @ sk_A)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['10', '21'])).
% 26.03/26.28  thf(t29_relset_1, axiom,
% 26.03/26.28    (![A:$i]:
% 26.03/26.28     ( m1_subset_1 @
% 26.03/26.28       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 26.03/26.28  thf('23', plain,
% 26.03/26.28      (![X29 : $i]:
% 26.03/26.28         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 26.03/26.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 26.03/26.28      inference('cnf', [status(esa)], [t29_relset_1])).
% 26.03/26.28  thf(redefinition_k6_partfun1, axiom,
% 26.03/26.28    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 26.03/26.28  thf('24', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 26.03/26.28  thf('25', plain,
% 26.03/26.28      (![X29 : $i]:
% 26.03/26.28         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 26.03/26.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 26.03/26.28      inference('demod', [status(thm)], ['23', '24'])).
% 26.03/26.28  thf('26', plain,
% 26.03/26.28      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 26.03/26.28         = (k6_partfun1 @ sk_A))),
% 26.03/26.28      inference('demod', [status(thm)], ['22', '25'])).
% 26.03/26.28  thf('27', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 26.03/26.28      inference('demod', [status(thm)], ['8', '9', '26'])).
% 26.03/26.28  thf('28', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(cc2_relset_1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.03/26.28       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 26.03/26.28  thf('29', plain,
% 26.03/26.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 26.03/26.28         ((v5_relat_1 @ X16 @ X18)
% 26.03/26.28          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc2_relset_1])).
% 26.03/26.28  thf('30', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 26.03/26.28      inference('sup-', [status(thm)], ['28', '29'])).
% 26.03/26.28  thf(d19_relat_1, axiom,
% 26.03/26.28    (![A:$i,B:$i]:
% 26.03/26.28     ( ( v1_relat_1 @ B ) =>
% 26.03/26.28       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 26.03/26.28  thf('31', plain,
% 26.03/26.28      (![X5 : $i, X6 : $i]:
% 26.03/26.28         (~ (v5_relat_1 @ X5 @ X6)
% 26.03/26.28          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 26.03/26.28          | ~ (v1_relat_1 @ X5))),
% 26.03/26.28      inference('cnf', [status(esa)], [d19_relat_1])).
% 26.03/26.28  thf('32', plain,
% 26.03/26.28      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 26.03/26.28      inference('sup-', [status(thm)], ['30', '31'])).
% 26.03/26.28  thf('33', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(cc1_relset_1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.03/26.28       ( v1_relat_1 @ C ) ))).
% 26.03/26.28  thf('34', plain,
% 26.03/26.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.03/26.28         ((v1_relat_1 @ X13)
% 26.03/26.28          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc1_relset_1])).
% 26.03/26.28  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 26.03/26.28      inference('sup-', [status(thm)], ['33', '34'])).
% 26.03/26.28  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 26.03/26.28      inference('demod', [status(thm)], ['32', '35'])).
% 26.03/26.28  thf(d1_funct_2, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.03/26.28       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 26.03/26.28           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 26.03/26.28             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 26.03/26.28         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 26.03/26.28           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 26.03/26.28             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 26.03/26.28  thf(zf_stmt_1, axiom,
% 26.03/26.28    (![B:$i,A:$i]:
% 26.03/26.28     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 26.03/26.28       ( zip_tseitin_0 @ B @ A ) ))).
% 26.03/26.28  thf('37', plain,
% 26.03/26.28      (![X30 : $i, X31 : $i]:
% 26.03/26.28         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.03/26.28  thf(t113_zfmisc_1, axiom,
% 26.03/26.28    (![A:$i,B:$i]:
% 26.03/26.28     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 26.03/26.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 26.03/26.28  thf('38', plain,
% 26.03/26.28      (![X1 : $i, X2 : $i]:
% 26.03/26.28         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 26.03/26.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 26.03/26.28  thf('39', plain,
% 26.03/26.28      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 26.03/26.28      inference('simplify', [status(thm)], ['38'])).
% 26.03/26.28  thf('40', plain,
% 26.03/26.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.03/26.28         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 26.03/26.28      inference('sup+', [status(thm)], ['37', '39'])).
% 26.03/26.28  thf('41', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(cc1_subset_1, axiom,
% 26.03/26.28    (![A:$i]:
% 26.03/26.28     ( ( v1_xboole_0 @ A ) =>
% 26.03/26.28       ( ![B:$i]:
% 26.03/26.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 26.03/26.28  thf('42', plain,
% 26.03/26.28      (![X3 : $i, X4 : $i]:
% 26.03/26.28         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 26.03/26.28          | (v1_xboole_0 @ X3)
% 26.03/26.28          | ~ (v1_xboole_0 @ X4))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc1_subset_1])).
% 26.03/26.28  thf('43', plain,
% 26.03/26.28      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['41', '42'])).
% 26.03/26.28  thf('44', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         (~ (v1_xboole_0 @ k1_xboole_0)
% 26.03/26.28          | (zip_tseitin_0 @ sk_A @ X0)
% 26.03/26.28          | (v1_xboole_0 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['40', '43'])).
% 26.03/26.28  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 26.03/26.28  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 26.03/26.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 26.03/26.28  thf('46', plain,
% 26.03/26.28      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ sk_C))),
% 26.03/26.28      inference('demod', [status(thm)], ['44', '45'])).
% 26.03/26.28  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 26.03/26.28      inference('sup-', [status(thm)], ['33', '34'])).
% 26.03/26.28  thf(cc1_funct_1, axiom,
% 26.03/26.28    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 26.03/26.28  thf('48', plain, (![X7 : $i]: ((v1_funct_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc1_funct_1])).
% 26.03/26.28  thf(cc2_funct_1, axiom,
% 26.03/26.28    (![A:$i]:
% 26.03/26.28     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 26.03/26.28       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 26.03/26.28  thf('49', plain,
% 26.03/26.28      (![X8 : $i]:
% 26.03/26.28         ((v2_funct_1 @ X8)
% 26.03/26.28          | ~ (v1_funct_1 @ X8)
% 26.03/26.28          | ~ (v1_relat_1 @ X8)
% 26.03/26.28          | ~ (v1_xboole_0 @ X8))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc2_funct_1])).
% 26.03/26.28  thf('50', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         (~ (v1_xboole_0 @ X0)
% 26.03/26.28          | ~ (v1_xboole_0 @ X0)
% 26.03/26.28          | ~ (v1_relat_1 @ X0)
% 26.03/26.28          | (v2_funct_1 @ X0))),
% 26.03/26.28      inference('sup-', [status(thm)], ['48', '49'])).
% 26.03/26.28  thf('51', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 26.03/26.28      inference('simplify', [status(thm)], ['50'])).
% 26.03/26.28  thf('52', plain, ((~ (v1_xboole_0 @ sk_C) | (v2_funct_1 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['47', '51'])).
% 26.03/26.28  thf('53', plain,
% 26.03/26.28      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v2_funct_1 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['46', '52'])).
% 26.03/26.28  thf('54', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('split', [status(esa)], ['0'])).
% 26.03/26.28  thf('55', plain,
% 26.03/26.28      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)) <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['53', '54'])).
% 26.03/26.28  thf('56', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 26.03/26.28  thf(zf_stmt_3, axiom,
% 26.03/26.28    (![C:$i,B:$i,A:$i]:
% 26.03/26.28     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 26.03/26.28       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 26.03/26.28  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 26.03/26.28  thf(zf_stmt_5, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.03/26.28       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 26.03/26.28         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 26.03/26.28           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 26.03/26.28             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 26.03/26.28  thf('57', plain,
% 26.03/26.28      (![X35 : $i, X36 : $i, X37 : $i]:
% 26.03/26.28         (~ (zip_tseitin_0 @ X35 @ X36)
% 26.03/26.28          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 26.03/26.28          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_5])).
% 26.03/26.28  thf('58', plain,
% 26.03/26.28      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 26.03/26.28      inference('sup-', [status(thm)], ['56', '57'])).
% 26.03/26.28  thf('59', plain,
% 26.03/26.28      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)) <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['55', '58'])).
% 26.03/26.28  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('61', plain,
% 26.03/26.28      (![X32 : $i, X33 : $i, X34 : $i]:
% 26.03/26.28         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 26.03/26.28          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 26.03/26.28          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.03/26.28  thf('62', plain,
% 26.03/26.28      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 26.03/26.28        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['60', '61'])).
% 26.03/26.28  thf('63', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(redefinition_k1_relset_1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.03/26.28       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 26.03/26.28  thf('64', plain,
% 26.03/26.28      (![X19 : $i, X20 : $i, X21 : $i]:
% 26.03/26.28         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 26.03/26.28          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 26.03/26.28  thf('65', plain,
% 26.03/26.28      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 26.03/26.28      inference('sup-', [status(thm)], ['63', '64'])).
% 26.03/26.28  thf('66', plain,
% 26.03/26.28      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 26.03/26.28      inference('demod', [status(thm)], ['62', '65'])).
% 26.03/26.28  thf('67', plain,
% 26.03/26.28      ((((sk_B) = (k1_relat_1 @ sk_D))) <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['59', '66'])).
% 26.03/26.28  thf(t47_funct_1, axiom,
% 26.03/26.28    (![A:$i]:
% 26.03/26.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 26.03/26.28       ( ![B:$i]:
% 26.03/26.28         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 26.03/26.28           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 26.03/26.28               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 26.03/26.28             ( v2_funct_1 @ B ) ) ) ) ))).
% 26.03/26.28  thf('68', plain,
% 26.03/26.28      (![X11 : $i, X12 : $i]:
% 26.03/26.28         (~ (v1_relat_1 @ X11)
% 26.03/26.28          | ~ (v1_funct_1 @ X11)
% 26.03/26.28          | (v2_funct_1 @ X11)
% 26.03/26.28          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X12))
% 26.03/26.28          | ~ (v2_funct_1 @ (k5_relat_1 @ X11 @ X12))
% 26.03/26.28          | ~ (v1_funct_1 @ X12)
% 26.03/26.28          | ~ (v1_relat_1 @ X12))),
% 26.03/26.28      inference('cnf', [status(esa)], [t47_funct_1])).
% 26.03/26.28  thf('69', plain,
% 26.03/26.28      ((![X0 : $i]:
% 26.03/26.28          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 26.03/26.28           | ~ (v1_relat_1 @ sk_D)
% 26.03/26.28           | ~ (v1_funct_1 @ sk_D)
% 26.03/26.28           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 26.03/26.28           | (v2_funct_1 @ X0)
% 26.03/26.28           | ~ (v1_funct_1 @ X0)
% 26.03/26.28           | ~ (v1_relat_1 @ X0)))
% 26.03/26.28         <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['67', '68'])).
% 26.03/26.28  thf('70', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('71', plain,
% 26.03/26.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.03/26.28         ((v1_relat_1 @ X13)
% 26.03/26.28          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc1_relset_1])).
% 26.03/26.28  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 26.03/26.28      inference('sup-', [status(thm)], ['70', '71'])).
% 26.03/26.28  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('74', plain,
% 26.03/26.28      ((![X0 : $i]:
% 26.03/26.28          (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 26.03/26.28           | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 26.03/26.28           | (v2_funct_1 @ X0)
% 26.03/26.28           | ~ (v1_funct_1 @ X0)
% 26.03/26.28           | ~ (v1_relat_1 @ X0)))
% 26.03/26.28         <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('demod', [status(thm)], ['69', '72', '73'])).
% 26.03/26.28  thf('75', plain,
% 26.03/26.28      (((~ (v1_relat_1 @ sk_C)
% 26.03/26.28         | ~ (v1_funct_1 @ sk_C)
% 26.03/26.28         | (v2_funct_1 @ sk_C)
% 26.03/26.28         | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 26.03/26.28         <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['36', '74'])).
% 26.03/26.28  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 26.03/26.28      inference('sup-', [status(thm)], ['33', '34'])).
% 26.03/26.28  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('78', plain,
% 26.03/26.28      ((((v2_funct_1 @ sk_C) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 26.03/26.28         <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('demod', [status(thm)], ['75', '76', '77'])).
% 26.03/26.28  thf('79', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('split', [status(esa)], ['0'])).
% 26.03/26.28  thf('80', plain,
% 26.03/26.28      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 26.03/26.28         <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('clc', [status(thm)], ['78', '79'])).
% 26.03/26.28  thf('81', plain,
% 26.03/26.28      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))) <= (~ ((v2_funct_1 @ sk_C)))),
% 26.03/26.28      inference('sup-', [status(thm)], ['27', '80'])).
% 26.03/26.28  thf(fc4_funct_1, axiom,
% 26.03/26.28    (![A:$i]:
% 26.03/26.28     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 26.03/26.28       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 26.03/26.28  thf('82', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 26.03/26.28      inference('cnf', [status(esa)], [fc4_funct_1])).
% 26.03/26.28  thf('83', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 26.03/26.28  thf('84', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 26.03/26.28      inference('demod', [status(thm)], ['82', '83'])).
% 26.03/26.28  thf('85', plain, (((v2_funct_1 @ sk_C))),
% 26.03/26.28      inference('demod', [status(thm)], ['81', '84'])).
% 26.03/26.28  thf('86', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 26.03/26.28      inference('split', [status(esa)], ['0'])).
% 26.03/26.28  thf('87', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 26.03/26.28      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 26.03/26.28  thf('88', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 26.03/26.28      inference('simpl_trail', [status(thm)], ['1', '87'])).
% 26.03/26.28  thf('89', plain,
% 26.03/26.28      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 26.03/26.28         = (k6_partfun1 @ sk_A))),
% 26.03/26.28      inference('demod', [status(thm)], ['22', '25'])).
% 26.03/26.28  thf('90', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(t24_funct_2, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 26.03/26.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.03/26.28       ( ![D:$i]:
% 26.03/26.28         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 26.03/26.28             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 26.03/26.28           ( ( r2_relset_1 @
% 26.03/26.28               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 26.03/26.28               ( k6_partfun1 @ B ) ) =>
% 26.03/26.28             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 26.03/26.28  thf('91', plain,
% 26.03/26.28      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 26.03/26.28         (~ (v1_funct_1 @ X53)
% 26.03/26.28          | ~ (v1_funct_2 @ X53 @ X54 @ X55)
% 26.03/26.28          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 26.03/26.28          | ~ (r2_relset_1 @ X54 @ X54 @ 
% 26.03/26.28               (k1_partfun1 @ X54 @ X55 @ X55 @ X54 @ X53 @ X56) @ 
% 26.03/26.28               (k6_partfun1 @ X54))
% 26.03/26.28          | ((k2_relset_1 @ X55 @ X54 @ X56) = (X54))
% 26.03/26.28          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 26.03/26.28          | ~ (v1_funct_2 @ X56 @ X55 @ X54)
% 26.03/26.28          | ~ (v1_funct_1 @ X56))),
% 26.03/26.28      inference('cnf', [status(esa)], [t24_funct_2])).
% 26.03/26.28  thf('92', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         (~ (v1_funct_1 @ X0)
% 26.03/26.28          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 26.03/26.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 26.03/26.28          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 26.03/26.28          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.03/26.28               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 26.03/26.28               (k6_partfun1 @ sk_A))
% 26.03/26.28          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 26.03/26.28          | ~ (v1_funct_1 @ sk_C))),
% 26.03/26.28      inference('sup-', [status(thm)], ['90', '91'])).
% 26.03/26.28  thf('93', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('95', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         (~ (v1_funct_1 @ X0)
% 26.03/26.28          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 26.03/26.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 26.03/26.28          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 26.03/26.28          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.03/26.28               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 26.03/26.28               (k6_partfun1 @ sk_A)))),
% 26.03/26.28      inference('demod', [status(thm)], ['92', '93', '94'])).
% 26.03/26.28  thf('96', plain,
% 26.03/26.28      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 26.03/26.28           (k6_partfun1 @ sk_A))
% 26.03/26.28        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 26.03/26.28        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 26.03/26.28        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 26.03/26.28        | ~ (v1_funct_1 @ sk_D))),
% 26.03/26.28      inference('sup-', [status(thm)], ['89', '95'])).
% 26.03/26.28  thf('97', plain,
% 26.03/26.28      (![X29 : $i]:
% 26.03/26.28         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 26.03/26.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 26.03/26.28      inference('demod', [status(thm)], ['23', '24'])).
% 26.03/26.28  thf('98', plain,
% 26.03/26.28      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 26.03/26.28         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 26.03/26.28          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 26.03/26.28          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 26.03/26.28          | ((X25) != (X28)))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 26.03/26.28  thf('99', plain,
% 26.03/26.28      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.03/26.28         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 26.03/26.28          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 26.03/26.28      inference('simplify', [status(thm)], ['98'])).
% 26.03/26.28  thf('100', plain,
% 26.03/26.28      (![X0 : $i]:
% 26.03/26.28         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 26.03/26.28      inference('sup-', [status(thm)], ['97', '99'])).
% 26.03/26.28  thf('101', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf(redefinition_k2_relset_1, axiom,
% 26.03/26.28    (![A:$i,B:$i,C:$i]:
% 26.03/26.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.03/26.28       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 26.03/26.28  thf('102', plain,
% 26.03/26.28      (![X22 : $i, X23 : $i, X24 : $i]:
% 26.03/26.28         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 26.03/26.28          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 26.03/26.28      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 26.03/26.28  thf('103', plain,
% 26.03/26.28      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 26.03/26.28      inference('sup-', [status(thm)], ['101', '102'])).
% 26.03/26.28  thf('104', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('107', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 26.03/26.28      inference('demod', [status(thm)],
% 26.03/26.28                ['96', '100', '103', '104', '105', '106'])).
% 26.03/26.28  thf(d3_funct_2, axiom,
% 26.03/26.28    (![A:$i,B:$i]:
% 26.03/26.28     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 26.03/26.28       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 26.03/26.28  thf('108', plain,
% 26.03/26.28      (![X38 : $i, X39 : $i]:
% 26.03/26.28         (((k2_relat_1 @ X39) != (X38))
% 26.03/26.28          | (v2_funct_2 @ X39 @ X38)
% 26.03/26.28          | ~ (v5_relat_1 @ X39 @ X38)
% 26.03/26.28          | ~ (v1_relat_1 @ X39))),
% 26.03/26.28      inference('cnf', [status(esa)], [d3_funct_2])).
% 26.03/26.28  thf('109', plain,
% 26.03/26.28      (![X39 : $i]:
% 26.03/26.28         (~ (v1_relat_1 @ X39)
% 26.03/26.28          | ~ (v5_relat_1 @ X39 @ (k2_relat_1 @ X39))
% 26.03/26.28          | (v2_funct_2 @ X39 @ (k2_relat_1 @ X39)))),
% 26.03/26.28      inference('simplify', [status(thm)], ['108'])).
% 26.03/26.28  thf('110', plain,
% 26.03/26.28      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 26.03/26.28        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 26.03/26.28        | ~ (v1_relat_1 @ sk_D))),
% 26.03/26.28      inference('sup-', [status(thm)], ['107', '109'])).
% 26.03/26.28  thf('111', plain,
% 26.03/26.28      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 26.03/26.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.03/26.28  thf('112', plain,
% 26.03/26.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 26.03/26.28         ((v5_relat_1 @ X16 @ X18)
% 26.03/26.28          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 26.03/26.28      inference('cnf', [status(esa)], [cc2_relset_1])).
% 26.03/26.28  thf('113', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 26.03/26.28      inference('sup-', [status(thm)], ['111', '112'])).
% 26.03/26.28  thf('114', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 26.03/26.28      inference('demod', [status(thm)],
% 26.03/26.28                ['96', '100', '103', '104', '105', '106'])).
% 26.03/26.28  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 26.03/26.28      inference('sup-', [status(thm)], ['70', '71'])).
% 26.03/26.28  thf('116', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 26.03/26.28      inference('demod', [status(thm)], ['110', '113', '114', '115'])).
% 26.03/26.28  thf('117', plain, ($false), inference('demod', [status(thm)], ['88', '116'])).
% 26.03/26.28  
% 26.03/26.28  % SZS output end Refutation
% 26.03/26.28  
% 26.03/26.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
