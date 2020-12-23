%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.szafugLX1h

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:11 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  342 (1291 expanded)
%              Number of leaves         :   66 ( 412 expanded)
%              Depth                    :   27
%              Number of atoms          : 3015 (29536 expanded)
%              Number of equality atoms :  172 (1808 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X57 @ X58 @ X60 @ X61 @ X56 @ X59 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( X50 = X53 )
      | ~ ( r2_relset_1 @ X51 @ X52 @ X50 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('15',plain,(
    ! [X63: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X63 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_funct_2,axiom,(
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

thf('18',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_funct_2 @ X71 @ X72 @ X73 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) )
      | ( v2_funct_2 @ X71 @ X73 )
      | ~ ( r2_relset_1 @ X73 @ X73 @ ( k1_partfun1 @ X73 @ X72 @ X72 @ X73 @ X74 @ X71 ) @ ( k6_partfun1 @ X73 ) )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X73 @ X72 ) ) )
      | ~ ( v1_funct_2 @ X74 @ X73 @ X72 )
      | ~ ( v1_funct_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X63: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X63 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( r2_relset_1 @ X51 @ X52 @ X50 @ X53 )
      | ( X50 != X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_relset_1 @ X51 @ X52 @ X53 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['23','27','28','29','30'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('32',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v2_funct_2 @ X55 @ X54 )
      | ( ( k2_relat_1 @ X55 )
        = X54 )
      | ~ ( v5_relat_1 @ X55 @ X54 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v5_relat_1 @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('43',plain,(
    ! [X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('44',plain,(
    ! [X25: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('45',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X26: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X26: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t183_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) @ ( k10_relat_1 @ ( k4_relat_1 @ B ) @ ( k10_relat_1 @ B @ A ) ) ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X27 ) @ X28 ) @ ( k10_relat_1 @ ( k4_relat_1 @ X27 ) @ ( k10_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t183_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','59'])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','62'])).

thf('64',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['68','69'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('74',plain,(
    ! [X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('75',plain,(
    ! [X25: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('76',plain,(
    ! [X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['77'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','91'])).

thf('93',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['73','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('99',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','99'])).

thf('101',plain,(
    ! [X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('102',plain,(
    ! [X29: $i] :
      ( ( r1_tarski @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_tarski @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('108',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k4_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['107','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('116',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_D ) ) )
    | ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('120',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['106','120'])).

thf('122',plain,
    ( ( r1_tarski @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['1','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('124',plain,(
    r1_tarski @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,(
    m1_subset_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('128',plain,(
    ! [X29: $i] :
      ( ( r1_tarski @ X29 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('129',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( X50 = X53 )
      | ~ ( r2_relset_1 @ X51 @ X52 @ X50 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) )
      | ( sk_D = X0 )
      | ~ ( r2_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('135',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_A ) ) )
      | ( sk_D = X0 )
      | ~ ( r2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ~ ( r2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ( sk_D
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['126','136'])).

thf('138',plain,
    ( ~ ( r2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['0','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('141',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_relset_1 @ X51 @ X52 @ X53 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( r2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['139','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('145',plain,(
    r2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_A @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('147',plain,
    ( sk_D
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['138','145','146'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('148',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_funct_1 @ X38 )
        = ( k4_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('149',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
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

thf('151',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( ( k1_partfun1 @ X65 @ X66 @ X68 @ X69 @ X64 @ X67 )
        = ( k5_relat_1 @ X64 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('158',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('159',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_funct_1 @ X45 )
      | ( X45
        = ( k2_funct_1 @ X46 ) )
      | ( ( k5_relat_1 @ X45 @ X46 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X46 ) ) )
      | ( ( k2_relat_1 @ X45 )
       != ( k1_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('160',plain,(
    ! [X70: $i] :
      ( ( k6_partfun1 @ X70 )
      = ( k6_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('161',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_funct_1 @ X45 )
      | ( X45
        = ( k2_funct_1 @ X46 ) )
      | ( ( k5_relat_1 @ X45 @ X46 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X46 ) ) )
      | ( ( k2_relat_1 @ X45 )
       != ( k1_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('165',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('167',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ( X84 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X85 )
      | ~ ( v1_funct_2 @ X85 @ X86 @ X84 )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X84 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X85 ) @ X85 )
        = ( k6_partfun1 @ X84 ) )
      | ~ ( v2_funct_1 @ X85 )
      | ( ( k2_relset_1 @ X86 @ X84 @ X85 )
       != X84 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('168',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('177',plain,(
    ! [X44: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X44 ) @ X44 ) )
        = ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('178',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('179',plain,(
    ! [X34: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('180',plain,(
    ! [X70: $i] :
      ( ( k6_partfun1 @ X70 )
      = ( k6_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('181',plain,(
    ! [X34: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X34 ) )
      = X34 ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','181','186','187','188'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['184','185'])).

thf('192',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','189','190','191'])).

thf('193',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v4_relat_1 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('196',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('198',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('200',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('202',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('204',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ~ ( v1_funct_1 @ X41 )
      | ( r1_tarski @ ( k2_relat_1 @ X41 ) @ ( k1_relat_1 @ X42 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X41 @ X42 ) )
       != ( k1_relat_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('205',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('207',plain,(
    ! [X70: $i] :
      ( ( k6_partfun1 @ X70 )
      = ( k6_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('208',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ( X84 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X85 )
      | ~ ( v1_funct_2 @ X85 @ X86 @ X84 )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X84 ) ) )
      | ( ( k5_relat_1 @ X85 @ ( k2_funct_1 @ X85 ) )
        = ( k6_partfun1 @ X86 ) )
      | ~ ( v2_funct_1 @ X85 )
      | ( ( k2_relset_1 @ X86 @ X84 @ X85 )
       != X84 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('211',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['211','212','213','214','215'])).

thf('217',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['217','218'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('220',plain,(
    ! [X43: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X43 @ ( k2_funct_1 @ X43 ) ) )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('221',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X34: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X34 ) )
      = X34 ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['184','185'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['221','222','223','224','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('228',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','181','186','187','188'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['184','185'])).

thf('232',plain,
    ( ( sk_A != sk_A )
    | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['205','208','226','227','228','229','230','231'])).

thf('233',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['202','233'])).

thf('235',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['193','234'])).

thf('236',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('238',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('239',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i,X83: $i] :
      ( ~ ( v1_funct_1 @ X79 )
      | ~ ( v1_funct_2 @ X79 @ X80 @ X81 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X80 @ X81 ) ) )
      | ( zip_tseitin_0 @ X79 @ X82 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X83 @ X80 @ X80 @ X81 @ X82 @ X79 ) )
      | ( zip_tseitin_1 @ X81 @ X80 )
      | ( ( k2_relset_1 @ X83 @ X80 @ X82 )
       != X80 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X80 ) ) )
      | ~ ( v1_funct_2 @ X82 @ X83 @ X80 )
      | ~ ( v1_funct_1 @ X82 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['237','243'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('245',plain,(
    ! [X40: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('246',plain,(
    ! [X70: $i] :
      ( ( k6_partfun1 @ X70 )
      = ( k6_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('247',plain,(
    ! [X40: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X40 ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['244','247','248','249','250','251'])).

thf('253',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,(
    ! [X77: $i,X78: $i] :
      ( ( X77 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('255',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X75: $i,X76: $i] :
      ( ( v2_funct_1 @ X76 )
      | ~ ( zip_tseitin_0 @ X76 @ X75 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('259',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['236','259'])).

thf('261',plain,
    ( ( sk_C
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['148','260'])).

thf('262',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('263',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['257','258'])).

thf('265',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['261','262','263','264'])).

thf('266',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','265'])).

thf('267',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_funct_1 @ X38 )
        = ( k4_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('268',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['184','185'])).

thf('271',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['269','270','271','272'])).

thf('274',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['266','273'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.szafugLX1h
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:55:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 2.82/3.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.03  % Solved by: fo/fo7.sh
% 2.82/3.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.03  % done 3500 iterations in 2.521s
% 2.82/3.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.03  % SZS output start Refutation
% 2.82/3.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.82/3.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.82/3.03  thf(sk_C_type, type, sk_C: $i).
% 2.82/3.03  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.82/3.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.82/3.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.82/3.03  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.82/3.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.82/3.03  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.82/3.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.82/3.03  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.82/3.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.82/3.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.82/3.03  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.82/3.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.82/3.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.82/3.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.82/3.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.82/3.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.82/3.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.82/3.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.82/3.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.82/3.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.82/3.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.82/3.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.82/3.03  thf(sk_D_type, type, sk_D: $i).
% 2.82/3.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.82/3.03  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.82/3.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.82/3.03  thf(involutiveness_k4_relat_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 2.82/3.03  thf('0', plain,
% 2.82/3.03      (![X25 : $i]:
% 2.82/3.03         (((k4_relat_1 @ (k4_relat_1 @ X25)) = (X25)) | ~ (v1_relat_1 @ X25))),
% 2.82/3.03      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.82/3.03  thf(t37_relat_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ A ) =>
% 2.82/3.03       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.82/3.03         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.82/3.03  thf('1', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k1_relat_1 @ X30) = (k2_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf(t36_funct_2, conjecture,
% 2.82/3.03    (![A:$i,B:$i,C:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ![D:$i]:
% 2.82/3.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.82/3.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.82/3.03           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.82/3.03               ( r2_relset_1 @
% 2.82/3.03                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.82/3.03                 ( k6_partfun1 @ A ) ) & 
% 2.82/3.03               ( v2_funct_1 @ C ) ) =>
% 2.82/3.03             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.82/3.03               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.82/3.03  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.03    (~( ![A:$i,B:$i,C:$i]:
% 2.82/3.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03          ( ![D:$i]:
% 2.82/3.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.82/3.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.82/3.03              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.82/3.03                  ( r2_relset_1 @
% 2.82/3.03                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.82/3.03                    ( k6_partfun1 @ A ) ) & 
% 2.82/3.03                  ( v2_funct_1 @ C ) ) =>
% 2.82/3.03                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.82/3.03                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.82/3.03    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.82/3.03  thf('2', plain,
% 2.82/3.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.03        (k6_partfun1 @ sk_A))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('3', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('4', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(dt_k1_partfun1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ E ) & 
% 2.82/3.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.82/3.03         ( v1_funct_1 @ F ) & 
% 2.82/3.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.82/3.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.82/3.03         ( m1_subset_1 @
% 2.82/3.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.82/3.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.82/3.03  thf('5', plain,
% 2.82/3.03      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 2.82/3.03          | ~ (v1_funct_1 @ X56)
% 2.82/3.03          | ~ (v1_funct_1 @ X59)
% 2.82/3.03          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 2.82/3.03          | (m1_subset_1 @ (k1_partfun1 @ X57 @ X58 @ X60 @ X61 @ X56 @ X59) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X61))))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.82/3.03  thf('6', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.82/3.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.82/3.03          | ~ (v1_funct_1 @ X1)
% 2.82/3.03          | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['4', '5'])).
% 2.82/3.03  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('8', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.82/3.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.82/3.03          | ~ (v1_funct_1 @ X1))),
% 2.82/3.03      inference('demod', [status(thm)], ['6', '7'])).
% 2.82/3.03  thf('9', plain,
% 2.82/3.03      ((~ (v1_funct_1 @ sk_D)
% 2.82/3.03        | (m1_subset_1 @ 
% 2.82/3.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['3', '8'])).
% 2.82/3.03  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('11', plain,
% 2.82/3.03      ((m1_subset_1 @ 
% 2.82/3.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.82/3.03      inference('demod', [status(thm)], ['9', '10'])).
% 2.82/3.03  thf(redefinition_r2_relset_1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.82/3.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.82/3.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.82/3.03  thf('12', plain,
% 2.82/3.03      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 2.82/3.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 2.82/3.03          | ((X50) = (X53))
% 2.82/3.03          | ~ (r2_relset_1 @ X51 @ X52 @ X50 @ X53))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.82/3.03  thf('13', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.03             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.82/3.03          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['11', '12'])).
% 2.82/3.03  thf('14', plain,
% 2.82/3.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.82/3.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03            = (k6_partfun1 @ sk_A)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['2', '13'])).
% 2.82/3.03  thf(dt_k6_partfun1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( m1_subset_1 @
% 2.82/3.03         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.82/3.03       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.82/3.03  thf('15', plain,
% 2.82/3.03      (![X63 : $i]:
% 2.82/3.03         (m1_subset_1 @ (k6_partfun1 @ X63) @ 
% 2.82/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X63)))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.82/3.03  thf('16', plain,
% 2.82/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03         = (k6_partfun1 @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['14', '15'])).
% 2.82/3.03  thf('17', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(t29_funct_2, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ![D:$i]:
% 2.82/3.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.82/3.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.82/3.03           ( ( r2_relset_1 @
% 2.82/3.03               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.82/3.03               ( k6_partfun1 @ A ) ) =>
% 2.82/3.03             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.82/3.03  thf('18', plain,
% 2.82/3.03      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X71)
% 2.82/3.03          | ~ (v1_funct_2 @ X71 @ X72 @ X73)
% 2.82/3.03          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73)))
% 2.82/3.03          | (v2_funct_2 @ X71 @ X73)
% 2.82/3.03          | ~ (r2_relset_1 @ X73 @ X73 @ 
% 2.82/3.03               (k1_partfun1 @ X73 @ X72 @ X72 @ X73 @ X74 @ X71) @ 
% 2.82/3.03               (k6_partfun1 @ X73))
% 2.82/3.03          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X73 @ X72)))
% 2.82/3.03          | ~ (v1_funct_2 @ X74 @ X73 @ X72)
% 2.82/3.03          | ~ (v1_funct_1 @ X74))),
% 2.82/3.03      inference('cnf', [status(esa)], [t29_funct_2])).
% 2.82/3.03  thf('19', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.82/3.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.03               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 2.82/3.03               (k6_partfun1 @ sk_A))
% 2.82/3.03          | (v2_funct_2 @ sk_D @ sk_A)
% 2.82/3.03          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.82/3.03          | ~ (v1_funct_1 @ sk_D))),
% 2.82/3.03      inference('sup-', [status(thm)], ['17', '18'])).
% 2.82/3.03  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('22', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.82/3.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.03               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 2.82/3.03               (k6_partfun1 @ sk_A))
% 2.82/3.03          | (v2_funct_2 @ sk_D @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.82/3.03  thf('23', plain,
% 2.82/3.03      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 2.82/3.03           (k6_partfun1 @ sk_A))
% 2.82/3.03        | (v2_funct_2 @ sk_D @ sk_A)
% 2.82/3.03        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.82/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['16', '22'])).
% 2.82/3.03  thf('24', plain,
% 2.82/3.03      (![X63 : $i]:
% 2.82/3.03         (m1_subset_1 @ (k6_partfun1 @ X63) @ 
% 2.82/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X63)))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.82/3.03  thf('25', plain,
% 2.82/3.03      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 2.82/3.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 2.82/3.03          | (r2_relset_1 @ X51 @ X52 @ X50 @ X53)
% 2.82/3.03          | ((X50) != (X53)))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.82/3.03  thf('26', plain,
% 2.82/3.03      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.82/3.03         ((r2_relset_1 @ X51 @ X52 @ X53 @ X53)
% 2.82/3.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 2.82/3.03      inference('simplify', [status(thm)], ['25'])).
% 2.82/3.03  thf('27', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 2.82/3.03      inference('sup-', [status(thm)], ['24', '26'])).
% 2.82/3.03  thf('28', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('29', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('31', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.82/3.03      inference('demod', [status(thm)], ['23', '27', '28', '29', '30'])).
% 2.82/3.03  thf(d3_funct_2, axiom,
% 2.82/3.03    (![A:$i,B:$i]:
% 2.82/3.03     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.82/3.03       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.82/3.03  thf('32', plain,
% 2.82/3.03      (![X54 : $i, X55 : $i]:
% 2.82/3.03         (~ (v2_funct_2 @ X55 @ X54)
% 2.82/3.03          | ((k2_relat_1 @ X55) = (X54))
% 2.82/3.03          | ~ (v5_relat_1 @ X55 @ X54)
% 2.82/3.03          | ~ (v1_relat_1 @ X55))),
% 2.82/3.03      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.82/3.03  thf('33', plain,
% 2.82/3.03      ((~ (v1_relat_1 @ sk_D)
% 2.82/3.03        | ~ (v5_relat_1 @ sk_D @ sk_A)
% 2.82/3.03        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['31', '32'])).
% 2.82/3.03  thf('34', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(cc2_relat_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ A ) =>
% 2.82/3.03       ( ![B:$i]:
% 2.82/3.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.82/3.03  thf('35', plain,
% 2.82/3.03      (![X18 : $i, X19 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.82/3.03          | (v1_relat_1 @ X18)
% 2.82/3.03          | ~ (v1_relat_1 @ X19))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.82/3.03  thf('36', plain,
% 2.82/3.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup-', [status(thm)], ['34', '35'])).
% 2.82/3.03  thf(fc6_relat_1, axiom,
% 2.82/3.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.82/3.03  thf('37', plain,
% 2.82/3.03      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 2.82/3.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.82/3.03  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('39', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(cc2_relset_1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i]:
% 2.82/3.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.82/3.03  thf('40', plain,
% 2.82/3.03      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.82/3.03         ((v5_relat_1 @ X47 @ X49)
% 2.82/3.03          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.82/3.03  thf('41', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.82/3.03      inference('sup-', [status(thm)], ['39', '40'])).
% 2.82/3.03  thf('42', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('43', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k2_relat_1 @ X30) = (k1_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf('44', plain,
% 2.82/3.03      (![X25 : $i]:
% 2.82/3.03         (((k4_relat_1 @ (k4_relat_1 @ X25)) = (X25)) | ~ (v1_relat_1 @ X25))),
% 2.82/3.03      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.82/3.03  thf('45', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k1_relat_1 @ X30) = (k2_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf(t169_relat_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ A ) =>
% 2.82/3.03       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.82/3.03  thf('46', plain,
% 2.82/3.03      (![X26 : $i]:
% 2.82/3.03         (((k10_relat_1 @ X26 @ (k2_relat_1 @ X26)) = (k1_relat_1 @ X26))
% 2.82/3.03          | ~ (v1_relat_1 @ X26))),
% 2.82/3.03      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.82/3.03  thf('47', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.82/3.03            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['45', '46'])).
% 2.82/3.03  thf(dt_k4_relat_1, axiom,
% 2.82/3.03    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 2.82/3.03  thf('48', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('49', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | ((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.82/3.03              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 2.82/3.03      inference('clc', [status(thm)], ['47', '48'])).
% 2.82/3.03  thf('50', plain,
% 2.82/3.03      (![X26 : $i]:
% 2.82/3.03         (((k10_relat_1 @ X26 @ (k2_relat_1 @ X26)) = (k1_relat_1 @ X26))
% 2.82/3.03          | ~ (v1_relat_1 @ X26))),
% 2.82/3.03      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.82/3.03  thf(t183_relat_1, axiom,
% 2.82/3.03    (![A:$i,B:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ B ) =>
% 2.82/3.03       ( r1_tarski @
% 2.82/3.03         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) @ 
% 2.82/3.03         ( k10_relat_1 @ ( k4_relat_1 @ B ) @ ( k10_relat_1 @ B @ A ) ) ) ))).
% 2.82/3.03  thf('51', plain,
% 2.82/3.03      (![X27 : $i, X28 : $i]:
% 2.82/3.03         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X27) @ X28) @ 
% 2.82/3.03           (k10_relat_1 @ (k4_relat_1 @ X27) @ (k10_relat_1 @ X27 @ X28)))
% 2.82/3.03          | ~ (v1_relat_1 @ X27))),
% 2.82/3.03      inference('cnf', [status(esa)], [t183_relat_1])).
% 2.82/3.03  thf('52', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ 
% 2.82/3.03           (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ X0))),
% 2.82/3.03      inference('sup+', [status(thm)], ['50', '51'])).
% 2.82/3.03  thf(idempotence_k3_xboole_0, axiom,
% 2.82/3.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.82/3.03  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.82/3.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.82/3.03  thf('54', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.82/3.03           (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ X0))),
% 2.82/3.03      inference('demod', [status(thm)], ['52', '53'])).
% 2.82/3.03  thf('55', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.82/3.03             (k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 2.82/3.03      inference('simplify', [status(thm)], ['54'])).
% 2.82/3.03  thf('56', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ X0))),
% 2.82/3.03      inference('sup+', [status(thm)], ['49', '55'])).
% 2.82/3.03  thf('57', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 2.82/3.03      inference('simplify', [status(thm)], ['56'])).
% 2.82/3.03  thf(t3_subset, axiom,
% 2.82/3.03    (![A:$i,B:$i]:
% 2.82/3.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.82/3.03  thf('58', plain,
% 2.82/3.03      (![X15 : $i, X17 : $i]:
% 2.82/3.03         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('59', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ (k2_relat_1 @ X0) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['57', '58'])).
% 2.82/3.03  thf('60', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k1_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['44', '59'])).
% 2.82/3.03  thf('61', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('62', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 2.82/3.03      inference('clc', [status(thm)], ['60', '61'])).
% 2.82/3.03  thf('63', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['43', '62'])).
% 2.82/3.03  thf('64', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('65', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 2.82/3.03      inference('clc', [status(thm)], ['63', '64'])).
% 2.82/3.03  thf('66', plain,
% 2.82/3.03      (![X15 : $i, X16 : $i]:
% 2.82/3.03         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('67', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.82/3.03             (k2_relat_1 @ X0)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['65', '66'])).
% 2.82/3.03  thf('68', plain,
% 2.82/3.03      (((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))) @ sk_A)
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup+', [status(thm)], ['42', '67'])).
% 2.82/3.03  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('70', plain,
% 2.82/3.03      ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))) @ sk_A)),
% 2.82/3.03      inference('demod', [status(thm)], ['68', '69'])).
% 2.82/3.03  thf(d10_xboole_0, axiom,
% 2.82/3.03    (![A:$i,B:$i]:
% 2.82/3.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.82/3.03  thf('71', plain,
% 2.82/3.03      (![X1 : $i, X3 : $i]:
% 2.82/3.03         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 2.82/3.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.82/3.03  thf('72', plain,
% 2.82/3.03      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.82/3.03        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['70', '71'])).
% 2.82/3.03  thf('73', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('74', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k2_relat_1 @ X30) = (k1_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf('75', plain,
% 2.82/3.03      (![X25 : $i]:
% 2.82/3.03         (((k4_relat_1 @ (k4_relat_1 @ X25)) = (X25)) | ~ (v1_relat_1 @ X25))),
% 2.82/3.03      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.82/3.03  thf('76', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k2_relat_1 @ X30) = (k1_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf('77', plain,
% 2.82/3.03      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 2.82/3.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.82/3.03  thf('78', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 2.82/3.03      inference('simplify', [status(thm)], ['77'])).
% 2.82/3.03  thf(d18_relat_1, axiom,
% 2.82/3.03    (![A:$i,B:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ B ) =>
% 2.82/3.03       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.82/3.03  thf('79', plain,
% 2.82/3.03      (![X20 : $i, X21 : $i]:
% 2.82/3.03         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.82/3.03          | (v4_relat_1 @ X20 @ X21)
% 2.82/3.03          | ~ (v1_relat_1 @ X20))),
% 2.82/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.82/3.03  thf('80', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['78', '79'])).
% 2.82/3.03  thf('81', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['76', '80'])).
% 2.82/3.03  thf('82', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('83', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.82/3.03      inference('clc', [status(thm)], ['81', '82'])).
% 2.82/3.03  thf('84', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['75', '83'])).
% 2.82/3.03  thf('85', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('86', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.82/3.03      inference('clc', [status(thm)], ['84', '85'])).
% 2.82/3.03  thf('87', plain,
% 2.82/3.03      (![X20 : $i, X21 : $i]:
% 2.82/3.03         (~ (v4_relat_1 @ X20 @ X21)
% 2.82/3.03          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.82/3.03          | ~ (v1_relat_1 @ X20))),
% 2.82/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.82/3.03  thf('88', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['86', '87'])).
% 2.82/3.03  thf('89', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0))),
% 2.82/3.03      inference('simplify', [status(thm)], ['88'])).
% 2.82/3.03  thf('90', plain,
% 2.82/3.03      (![X15 : $i, X17 : $i]:
% 2.82/3.03         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('91', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['89', '90'])).
% 2.82/3.03  thf('92', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k2_relat_1 @ X0) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['74', '91'])).
% 2.82/3.03  thf('93', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('94', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ (k2_relat_1 @ X0) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))),
% 2.82/3.03      inference('clc', [status(thm)], ['92', '93'])).
% 2.82/3.03  thf('95', plain,
% 2.82/3.03      (![X15 : $i, X16 : $i]:
% 2.82/3.03         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('96', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.82/3.03             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['94', '95'])).
% 2.82/3.03  thf('97', plain,
% 2.82/3.03      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup+', [status(thm)], ['73', '96'])).
% 2.82/3.03  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('99', plain,
% 2.82/3.03      ((r1_tarski @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.82/3.03      inference('demod', [status(thm)], ['97', '98'])).
% 2.82/3.03  thf('100', plain,
% 2.82/3.03      (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.82/3.03      inference('demod', [status(thm)], ['72', '99'])).
% 2.82/3.03  thf('101', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k2_relat_1 @ X30) = (k1_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf(t21_relat_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v1_relat_1 @ A ) =>
% 2.82/3.03       ( r1_tarski @
% 2.82/3.03         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.82/3.03  thf('102', plain,
% 2.82/3.03      (![X29 : $i]:
% 2.82/3.03         ((r1_tarski @ X29 @ 
% 2.82/3.03           (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29)))
% 2.82/3.03          | ~ (v1_relat_1 @ X29))),
% 2.82/3.03      inference('cnf', [status(esa)], [t21_relat_1])).
% 2.82/3.03  thf('103', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.82/3.03           (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['101', '102'])).
% 2.82/3.03  thf('104', plain,
% 2.82/3.03      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.82/3.03  thf('105', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.82/3.03             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.82/3.03              (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.82/3.03      inference('clc', [status(thm)], ['103', '104'])).
% 2.82/3.03  thf('106', plain,
% 2.82/3.03      (((r1_tarski @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ 
% 2.82/3.03         (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A))
% 2.82/3.03        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.82/3.03      inference('sup+', [status(thm)], ['100', '105'])).
% 2.82/3.03  thf('107', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('108', plain,
% 2.82/3.03      (![X30 : $i]:
% 2.82/3.03         (((k1_relat_1 @ X30) = (k2_relat_1 @ (k4_relat_1 @ X30)))
% 2.82/3.03          | ~ (v1_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.82/3.03  thf('109', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.82/3.03             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.82/3.03              (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.82/3.03      inference('clc', [status(thm)], ['103', '104'])).
% 2.82/3.03  thf('110', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         ((r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.82/3.03           (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 2.82/3.03          | ~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ X0))),
% 2.82/3.03      inference('sup+', [status(thm)], ['108', '109'])).
% 2.82/3.03  thf('111', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.82/3.03             (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))),
% 2.82/3.03      inference('simplify', [status(thm)], ['110'])).
% 2.82/3.03  thf('112', plain,
% 2.82/3.03      (![X15 : $i, X17 : $i]:
% 2.82/3.03         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('113', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ (k4_relat_1 @ X0) @ 
% 2.82/3.03             (k1_zfmisc_1 @ 
% 2.82/3.03              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['111', '112'])).
% 2.82/3.03  thf('114', plain,
% 2.82/3.03      (((m1_subset_1 @ (k4_relat_1 @ sk_D) @ 
% 2.82/3.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_D))))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup+', [status(thm)], ['107', '113'])).
% 2.82/3.03  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('116', plain,
% 2.82/3.03      ((m1_subset_1 @ (k4_relat_1 @ sk_D) @ 
% 2.82/3.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_D))))),
% 2.82/3.03      inference('demod', [status(thm)], ['114', '115'])).
% 2.82/3.03  thf('117', plain,
% 2.82/3.03      (![X18 : $i, X19 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.82/3.03          | (v1_relat_1 @ X18)
% 2.82/3.03          | ~ (v1_relat_1 @ X19))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.82/3.03  thf('118', plain,
% 2.82/3.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_D)))
% 2.82/3.03        | (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['116', '117'])).
% 2.82/3.03  thf('119', plain,
% 2.82/3.03      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 2.82/3.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.82/3.03  thf('120', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['118', '119'])).
% 2.82/3.03  thf('121', plain,
% 2.82/3.03      ((r1_tarski @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ 
% 2.82/3.03        (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['106', '120'])).
% 2.82/3.03  thf('122', plain,
% 2.82/3.03      (((r1_tarski @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ 
% 2.82/3.03         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup+', [status(thm)], ['1', '121'])).
% 2.82/3.03  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('124', plain,
% 2.82/3.03      ((r1_tarski @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ 
% 2.82/3.03        (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['122', '123'])).
% 2.82/3.03  thf('125', plain,
% 2.82/3.03      (![X15 : $i, X17 : $i]:
% 2.82/3.03         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('126', plain,
% 2.82/3.03      ((m1_subset_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ 
% 2.82/3.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['124', '125'])).
% 2.82/3.03  thf('127', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('128', plain,
% 2.82/3.03      (![X29 : $i]:
% 2.82/3.03         ((r1_tarski @ X29 @ 
% 2.82/3.03           (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29)))
% 2.82/3.03          | ~ (v1_relat_1 @ X29))),
% 2.82/3.03      inference('cnf', [status(esa)], [t21_relat_1])).
% 2.82/3.03  thf('129', plain,
% 2.82/3.03      (![X15 : $i, X17 : $i]:
% 2.82/3.03         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.82/3.03      inference('cnf', [status(esa)], [t3_subset])).
% 2.82/3.03  thf('130', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ X0 @ 
% 2.82/3.03             (k1_zfmisc_1 @ 
% 2.82/3.03              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['128', '129'])).
% 2.82/3.03  thf('131', plain,
% 2.82/3.03      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 2.82/3.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 2.82/3.03          | ((X50) = (X53))
% 2.82/3.03          | ~ (r2_relset_1 @ X51 @ X52 @ X50 @ X53))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.82/3.03  thf('132', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | ~ (r2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 2.82/3.03          | ((X0) = (X1))
% 2.82/3.03          | ~ (m1_subset_1 @ X1 @ 
% 2.82/3.03               (k1_zfmisc_1 @ 
% 2.82/3.03                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['130', '131'])).
% 2.82/3.03  thf('133', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X0 @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))
% 2.82/3.03          | ((sk_D) = (X0))
% 2.82/3.03          | ~ (r2_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 2.82/3.03               sk_D @ X0)
% 2.82/3.03          | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup-', [status(thm)], ['127', '132'])).
% 2.82/3.03  thf('134', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('136', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X0 @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_A)))
% 2.82/3.03          | ((sk_D) = (X0))
% 2.82/3.03          | ~ (r2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D @ X0))),
% 2.82/3.03      inference('demod', [status(thm)], ['133', '134', '135'])).
% 2.82/3.03  thf('137', plain,
% 2.82/3.03      ((~ (r2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D @ 
% 2.82/3.03           (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.82/3.03        | ((sk_D) = (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['126', '136'])).
% 2.82/3.03  thf('138', plain,
% 2.82/3.03      ((~ (r2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D @ sk_D)
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D)
% 2.82/3.03        | ((sk_D) = (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['0', '137'])).
% 2.82/3.03  thf('139', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('140', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (m1_subset_1 @ X0 @ 
% 2.82/3.03             (k1_zfmisc_1 @ 
% 2.82/3.03              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['128', '129'])).
% 2.82/3.03  thf('141', plain,
% 2.82/3.03      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.82/3.03         ((r2_relset_1 @ X51 @ X52 @ X53 @ X53)
% 2.82/3.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 2.82/3.03      inference('simplify', [status(thm)], ['25'])).
% 2.82/3.03  thf('142', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X0)
% 2.82/3.03          | (r2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X0))),
% 2.82/3.03      inference('sup-', [status(thm)], ['140', '141'])).
% 2.82/3.03  thf('143', plain,
% 2.82/3.03      (((r2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D @ sk_D)
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.03      inference('sup+', [status(thm)], ['139', '142'])).
% 2.82/3.03  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('145', plain, ((r2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_A @ sk_D @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['143', '144'])).
% 2.82/3.03  thf('146', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('147', plain, (((sk_D) = (k4_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.82/3.03      inference('demod', [status(thm)], ['138', '145', '146'])).
% 2.82/3.03  thf(d9_funct_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.03       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.82/3.03  thf('148', plain,
% 2.82/3.03      (![X38 : $i]:
% 2.82/3.03         (~ (v2_funct_1 @ X38)
% 2.82/3.03          | ((k2_funct_1 @ X38) = (k4_relat_1 @ X38))
% 2.82/3.03          | ~ (v1_funct_1 @ X38)
% 2.82/3.03          | ~ (v1_relat_1 @ X38))),
% 2.82/3.03      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.82/3.03  thf('149', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('150', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(redefinition_k1_partfun1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ E ) & 
% 2.82/3.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.82/3.03         ( v1_funct_1 @ F ) & 
% 2.82/3.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.82/3.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.82/3.03  thf('151', plain,
% 2.82/3.03      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66)))
% 2.82/3.03          | ~ (v1_funct_1 @ X64)
% 2.82/3.03          | ~ (v1_funct_1 @ X67)
% 2.82/3.03          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 2.82/3.03          | ((k1_partfun1 @ X65 @ X66 @ X68 @ X69 @ X64 @ X67)
% 2.82/3.03              = (k5_relat_1 @ X64 @ X67)))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.82/3.03  thf('152', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.82/3.03            = (k5_relat_1 @ sk_C @ X0))
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.82/3.03          | ~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['150', '151'])).
% 2.82/3.03  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('154', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.82/3.03            = (k5_relat_1 @ sk_C @ X0))
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.82/3.03          | ~ (v1_funct_1 @ X0))),
% 2.82/3.03      inference('demod', [status(thm)], ['152', '153'])).
% 2.82/3.03  thf('155', plain,
% 2.82/3.03      ((~ (v1_funct_1 @ sk_D)
% 2.82/3.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['149', '154'])).
% 2.82/3.03  thf('156', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('157', plain,
% 2.82/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03         = (k6_partfun1 @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['14', '15'])).
% 2.82/3.03  thf('158', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['155', '156', '157'])).
% 2.82/3.03  thf(t64_funct_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.03       ( ![B:$i]:
% 2.82/3.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.82/3.03           ( ( ( v2_funct_1 @ A ) & 
% 2.82/3.03               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.82/3.03               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.82/3.03             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.82/3.03  thf('159', plain,
% 2.82/3.03      (![X45 : $i, X46 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X45)
% 2.82/3.03          | ~ (v1_funct_1 @ X45)
% 2.82/3.03          | ((X45) = (k2_funct_1 @ X46))
% 2.82/3.03          | ((k5_relat_1 @ X45 @ X46) != (k6_relat_1 @ (k2_relat_1 @ X46)))
% 2.82/3.03          | ((k2_relat_1 @ X45) != (k1_relat_1 @ X46))
% 2.82/3.03          | ~ (v2_funct_1 @ X46)
% 2.82/3.03          | ~ (v1_funct_1 @ X46)
% 2.82/3.03          | ~ (v1_relat_1 @ X46))),
% 2.82/3.03      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.82/3.03  thf(redefinition_k6_partfun1, axiom,
% 2.82/3.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.82/3.03  thf('160', plain, (![X70 : $i]: ((k6_partfun1 @ X70) = (k6_relat_1 @ X70))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.03  thf('161', plain,
% 2.82/3.03      (![X45 : $i, X46 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X45)
% 2.82/3.03          | ~ (v1_funct_1 @ X45)
% 2.82/3.03          | ((X45) = (k2_funct_1 @ X46))
% 2.82/3.03          | ((k5_relat_1 @ X45 @ X46) != (k6_partfun1 @ (k2_relat_1 @ X46)))
% 2.82/3.03          | ((k2_relat_1 @ X45) != (k1_relat_1 @ X46))
% 2.82/3.03          | ~ (v2_funct_1 @ X46)
% 2.82/3.03          | ~ (v1_funct_1 @ X46)
% 2.82/3.03          | ~ (v1_relat_1 @ X46))),
% 2.82/3.03      inference('demod', [status(thm)], ['159', '160'])).
% 2.82/3.03  thf('162', plain,
% 2.82/3.03      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_D)
% 2.82/3.03        | ~ (v2_funct_1 @ sk_D)
% 2.82/3.03        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.82/3.03        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ~ (v1_relat_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['158', '161'])).
% 2.82/3.03  thf('163', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['33', '38', '41'])).
% 2.82/3.03  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('165', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('166', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(t35_funct_2, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.82/3.03         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.82/3.03           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.82/3.03             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.82/3.03  thf('167', plain,
% 2.82/3.03      (![X84 : $i, X85 : $i, X86 : $i]:
% 2.82/3.03         (((X84) = (k1_xboole_0))
% 2.82/3.03          | ~ (v1_funct_1 @ X85)
% 2.82/3.03          | ~ (v1_funct_2 @ X85 @ X86 @ X84)
% 2.82/3.03          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X84)))
% 2.82/3.03          | ((k5_relat_1 @ (k2_funct_1 @ X85) @ X85) = (k6_partfun1 @ X84))
% 2.82/3.03          | ~ (v2_funct_1 @ X85)
% 2.82/3.03          | ((k2_relset_1 @ X86 @ X84 @ X85) != (X84)))),
% 2.82/3.03      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.82/3.03  thf('168', plain,
% 2.82/3.03      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.82/3.03        | ~ (v2_funct_1 @ sk_C)
% 2.82/3.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.82/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['166', '167'])).
% 2.82/3.03  thf('169', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('171', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('173', plain,
% 2.82/3.03      ((((sk_B) != (sk_B))
% 2.82/3.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.82/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.82/3.03      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 2.82/3.03  thf('174', plain,
% 2.82/3.03      ((((sk_B) = (k1_xboole_0))
% 2.82/3.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 2.82/3.03      inference('simplify', [status(thm)], ['173'])).
% 2.82/3.03  thf('175', plain, (((sk_B) != (k1_xboole_0))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('176', plain,
% 2.82/3.03      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.82/3.03      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 2.82/3.03  thf(t59_funct_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.03       ( ( v2_funct_1 @ A ) =>
% 2.82/3.03         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 2.82/3.03             ( k2_relat_1 @ A ) ) & 
% 2.82/3.03           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 2.82/3.03             ( k2_relat_1 @ A ) ) ) ) ))).
% 2.82/3.03  thf('177', plain,
% 2.82/3.03      (![X44 : $i]:
% 2.82/3.03         (~ (v2_funct_1 @ X44)
% 2.82/3.03          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X44) @ X44))
% 2.82/3.03              = (k2_relat_1 @ X44))
% 2.82/3.03          | ~ (v1_funct_1 @ X44)
% 2.82/3.03          | ~ (v1_relat_1 @ X44))),
% 2.82/3.03      inference('cnf', [status(esa)], [t59_funct_1])).
% 2.82/3.03  thf('178', plain,
% 2.82/3.03      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup+', [status(thm)], ['176', '177'])).
% 2.82/3.03  thf(t71_relat_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.82/3.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.82/3.03  thf('179', plain, (![X34 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 2.82/3.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.03  thf('180', plain, (![X70 : $i]: ((k6_partfun1 @ X70) = (k6_relat_1 @ X70))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.03  thf('181', plain,
% 2.82/3.03      (![X34 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X34)) = (X34))),
% 2.82/3.03      inference('demod', [status(thm)], ['179', '180'])).
% 2.82/3.03  thf('182', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('183', plain,
% 2.82/3.03      (![X18 : $i, X19 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.82/3.03          | (v1_relat_1 @ X18)
% 2.82/3.03          | ~ (v1_relat_1 @ X19))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.82/3.03  thf('184', plain,
% 2.82/3.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['182', '183'])).
% 2.82/3.03  thf('185', plain,
% 2.82/3.03      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 2.82/3.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.82/3.03  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.03      inference('demod', [status(thm)], ['184', '185'])).
% 2.82/3.03  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('189', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 2.82/3.03      inference('demod', [status(thm)], ['178', '181', '186', '187', '188'])).
% 2.82/3.03  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.03      inference('demod', [status(thm)], ['184', '185'])).
% 2.82/3.03  thf('192', plain,
% 2.82/3.03      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 2.82/3.03        | ~ (v2_funct_1 @ sk_D)
% 2.82/3.03        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.82/3.03        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.82/3.03      inference('demod', [status(thm)],
% 2.82/3.03                ['162', '163', '164', '165', '189', '190', '191'])).
% 2.82/3.03  thf('193', plain,
% 2.82/3.03      ((((sk_C) = (k2_funct_1 @ sk_D))
% 2.82/3.03        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.82/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.82/3.03      inference('simplify', [status(thm)], ['192'])).
% 2.82/3.03  thf('194', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('195', plain,
% 2.82/3.03      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.82/3.03         ((v4_relat_1 @ X47 @ X48)
% 2.82/3.03          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.82/3.03  thf('196', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 2.82/3.03      inference('sup-', [status(thm)], ['194', '195'])).
% 2.82/3.03  thf('197', plain,
% 2.82/3.03      (![X20 : $i, X21 : $i]:
% 2.82/3.03         (~ (v4_relat_1 @ X20 @ X21)
% 2.82/3.03          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.82/3.03          | ~ (v1_relat_1 @ X20))),
% 2.82/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.82/3.03  thf('198', plain,
% 2.82/3.03      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 2.82/3.03      inference('sup-', [status(thm)], ['196', '197'])).
% 2.82/3.03  thf('199', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('200', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 2.82/3.03      inference('demod', [status(thm)], ['198', '199'])).
% 2.82/3.03  thf('201', plain,
% 2.82/3.03      (![X1 : $i, X3 : $i]:
% 2.82/3.03         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 2.82/3.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.82/3.03  thf('202', plain,
% 2.82/3.03      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))
% 2.82/3.03        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['200', '201'])).
% 2.82/3.03  thf('203', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['155', '156', '157'])).
% 2.82/3.03  thf(t27_funct_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.03       ( ![B:$i]:
% 2.82/3.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.82/3.03           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 2.82/3.03             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 2.82/3.03  thf('204', plain,
% 2.82/3.03      (![X41 : $i, X42 : $i]:
% 2.82/3.03         (~ (v1_relat_1 @ X41)
% 2.82/3.03          | ~ (v1_funct_1 @ X41)
% 2.82/3.03          | (r1_tarski @ (k2_relat_1 @ X41) @ (k1_relat_1 @ X42))
% 2.82/3.03          | ((k1_relat_1 @ (k5_relat_1 @ X41 @ X42)) != (k1_relat_1 @ X41))
% 2.82/3.03          | ~ (v1_funct_1 @ X42)
% 2.82/3.03          | ~ (v1_relat_1 @ X42))),
% 2.82/3.03      inference('cnf', [status(esa)], [t27_funct_1])).
% 2.82/3.03  thf('205', plain,
% 2.82/3.03      ((((k1_relat_1 @ (k6_partfun1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_D)
% 2.82/3.03        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ~ (v1_relat_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['203', '204'])).
% 2.82/3.03  thf('206', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 2.82/3.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.03  thf('207', plain, (![X70 : $i]: ((k6_partfun1 @ X70) = (k6_relat_1 @ X70))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.03  thf('208', plain,
% 2.82/3.03      (![X33 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X33)) = (X33))),
% 2.82/3.03      inference('demod', [status(thm)], ['206', '207'])).
% 2.82/3.03  thf('209', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('210', plain,
% 2.82/3.03      (![X84 : $i, X85 : $i, X86 : $i]:
% 2.82/3.03         (((X84) = (k1_xboole_0))
% 2.82/3.03          | ~ (v1_funct_1 @ X85)
% 2.82/3.03          | ~ (v1_funct_2 @ X85 @ X86 @ X84)
% 2.82/3.03          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X84)))
% 2.82/3.03          | ((k5_relat_1 @ X85 @ (k2_funct_1 @ X85)) = (k6_partfun1 @ X86))
% 2.82/3.03          | ~ (v2_funct_1 @ X85)
% 2.82/3.03          | ((k2_relset_1 @ X86 @ X84 @ X85) != (X84)))),
% 2.82/3.03      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.82/3.03  thf('211', plain,
% 2.82/3.03      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.82/3.03        | ~ (v2_funct_1 @ sk_C)
% 2.82/3.03        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.82/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['209', '210'])).
% 2.82/3.03  thf('212', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('214', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('216', plain,
% 2.82/3.03      ((((sk_B) != (sk_B))
% 2.82/3.03        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.82/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.82/3.03      inference('demod', [status(thm)], ['211', '212', '213', '214', '215'])).
% 2.82/3.03  thf('217', plain,
% 2.82/3.03      ((((sk_B) = (k1_xboole_0))
% 2.82/3.03        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 2.82/3.03      inference('simplify', [status(thm)], ['216'])).
% 2.82/3.03  thf('218', plain, (((sk_B) != (k1_xboole_0))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('219', plain,
% 2.82/3.03      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 2.82/3.03      inference('simplify_reflect-', [status(thm)], ['217', '218'])).
% 2.82/3.03  thf(t58_funct_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.82/3.03       ( ( v2_funct_1 @ A ) =>
% 2.82/3.03         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 2.82/3.03             ( k1_relat_1 @ A ) ) & 
% 2.82/3.03           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 2.82/3.03             ( k1_relat_1 @ A ) ) ) ) ))).
% 2.82/3.03  thf('220', plain,
% 2.82/3.03      (![X43 : $i]:
% 2.82/3.03         (~ (v2_funct_1 @ X43)
% 2.82/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X43 @ (k2_funct_1 @ X43)))
% 2.82/3.03              = (k1_relat_1 @ X43))
% 2.82/3.03          | ~ (v1_funct_1 @ X43)
% 2.82/3.03          | ~ (v1_relat_1 @ X43))),
% 2.82/3.03      inference('cnf', [status(esa)], [t58_funct_1])).
% 2.82/3.03  thf('221', plain,
% 2.82/3.03      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup+', [status(thm)], ['219', '220'])).
% 2.82/3.03  thf('222', plain,
% 2.82/3.03      (![X34 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X34)) = (X34))),
% 2.82/3.03      inference('demod', [status(thm)], ['179', '180'])).
% 2.82/3.03  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.03      inference('demod', [status(thm)], ['184', '185'])).
% 2.82/3.03  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('225', plain, ((v2_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('226', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.82/3.03      inference('demod', [status(thm)], ['221', '222', '223', '224', '225'])).
% 2.82/3.03  thf('227', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('228', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('229', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 2.82/3.03      inference('demod', [status(thm)], ['178', '181', '186', '187', '188'])).
% 2.82/3.03  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.03      inference('demod', [status(thm)], ['184', '185'])).
% 2.82/3.03  thf('232', plain,
% 2.82/3.03      ((((sk_A) != (sk_A)) | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D)))),
% 2.82/3.03      inference('demod', [status(thm)],
% 2.82/3.03                ['205', '208', '226', '227', '228', '229', '230', '231'])).
% 2.82/3.03  thf('233', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))),
% 2.82/3.03      inference('simplify', [status(thm)], ['232'])).
% 2.82/3.03  thf('234', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['202', '233'])).
% 2.82/3.03  thf('235', plain,
% 2.82/3.03      ((((sk_C) = (k2_funct_1 @ sk_D))
% 2.82/3.03        | ((sk_B) != (sk_B))
% 2.82/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['193', '234'])).
% 2.82/3.03  thf('236', plain, ((~ (v2_funct_1 @ sk_D) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.82/3.03      inference('simplify', [status(thm)], ['235'])).
% 2.82/3.03  thf('237', plain,
% 2.82/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03         = (k6_partfun1 @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['14', '15'])).
% 2.82/3.03  thf('238', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(t30_funct_2, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.82/3.03     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.82/3.03         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.82/3.03       ( ![E:$i]:
% 2.82/3.03         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.82/3.03             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.82/3.03           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.82/3.03               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.82/3.03             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.82/3.03               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.82/3.03  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.82/3.03  thf(zf_stmt_2, axiom,
% 2.82/3.03    (![C:$i,B:$i]:
% 2.82/3.03     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.82/3.03       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.82/3.03  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.82/3.03  thf(zf_stmt_4, axiom,
% 2.82/3.03    (![E:$i,D:$i]:
% 2.82/3.03     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.82/3.03  thf(zf_stmt_5, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.82/3.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ![E:$i]:
% 2.82/3.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.82/3.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.82/3.03           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.82/3.03               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.82/3.03             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.82/3.03  thf('239', plain,
% 2.82/3.03      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X79)
% 2.82/3.03          | ~ (v1_funct_2 @ X79 @ X80 @ X81)
% 2.82/3.03          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X80 @ X81)))
% 2.82/3.03          | (zip_tseitin_0 @ X79 @ X82)
% 2.82/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X83 @ X80 @ X80 @ X81 @ X82 @ X79))
% 2.82/3.03          | (zip_tseitin_1 @ X81 @ X80)
% 2.82/3.03          | ((k2_relset_1 @ X83 @ X80 @ X82) != (X80))
% 2.82/3.03          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X80)))
% 2.82/3.03          | ~ (v1_funct_2 @ X82 @ X83 @ X80)
% 2.82/3.03          | ~ (v1_funct_1 @ X82))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.82/3.03  thf('240', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.82/3.03          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.82/3.03          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.82/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.82/3.03          | (zip_tseitin_0 @ sk_D @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.82/3.03          | ~ (v1_funct_1 @ sk_D))),
% 2.82/3.03      inference('sup-', [status(thm)], ['238', '239'])).
% 2.82/3.03  thf('241', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('242', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('243', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.82/3.03          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.82/3.03          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.82/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.82/3.03          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.82/3.03      inference('demod', [status(thm)], ['240', '241', '242'])).
% 2.82/3.03  thf('244', plain,
% 2.82/3.03      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.82/3.03        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.82/3.03        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.82/3.03        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.82/3.03        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.82/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['237', '243'])).
% 2.82/3.03  thf(fc4_funct_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.82/3.03       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.82/3.03  thf('245', plain, (![X40 : $i]: (v2_funct_1 @ (k6_relat_1 @ X40))),
% 2.82/3.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.82/3.03  thf('246', plain, (![X70 : $i]: ((k6_partfun1 @ X70) = (k6_relat_1 @ X70))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.03  thf('247', plain, (![X40 : $i]: (v2_funct_1 @ (k6_partfun1 @ X40))),
% 2.82/3.03      inference('demod', [status(thm)], ['245', '246'])).
% 2.82/3.03  thf('248', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('249', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('250', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('252', plain,
% 2.82/3.03      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.82/3.03        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.82/3.03        | ((sk_B) != (sk_B)))),
% 2.82/3.03      inference('demod', [status(thm)],
% 2.82/3.03                ['244', '247', '248', '249', '250', '251'])).
% 2.82/3.03  thf('253', plain,
% 2.82/3.03      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.82/3.03      inference('simplify', [status(thm)], ['252'])).
% 2.82/3.03  thf('254', plain,
% 2.82/3.03      (![X77 : $i, X78 : $i]:
% 2.82/3.03         (((X77) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X77 @ X78))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.82/3.03  thf('255', plain,
% 2.82/3.03      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['253', '254'])).
% 2.82/3.03  thf('256', plain, (((sk_A) != (k1_xboole_0))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('257', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.82/3.03      inference('simplify_reflect-', [status(thm)], ['255', '256'])).
% 2.82/3.03  thf('258', plain,
% 2.82/3.03      (![X75 : $i, X76 : $i]:
% 2.82/3.03         ((v2_funct_1 @ X76) | ~ (zip_tseitin_0 @ X76 @ X75))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.82/3.03  thf('259', plain, ((v2_funct_1 @ sk_D)),
% 2.82/3.03      inference('sup-', [status(thm)], ['257', '258'])).
% 2.82/3.03  thf('260', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['236', '259'])).
% 2.82/3.03  thf('261', plain,
% 2.82/3.03      ((((sk_C) = (k4_relat_1 @ sk_D))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_D)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_D)
% 2.82/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.82/3.03      inference('sup+', [status(thm)], ['148', '260'])).
% 2.82/3.03  thf('262', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.82/3.03  thf('263', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('264', plain, ((v2_funct_1 @ sk_D)),
% 2.82/3.03      inference('sup-', [status(thm)], ['257', '258'])).
% 2.82/3.03  thf('265', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 2.82/3.03      inference('demod', [status(thm)], ['261', '262', '263', '264'])).
% 2.82/3.03  thf('266', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 2.82/3.03      inference('demod', [status(thm)], ['147', '265'])).
% 2.82/3.03  thf('267', plain,
% 2.82/3.03      (![X38 : $i]:
% 2.82/3.03         (~ (v2_funct_1 @ X38)
% 2.82/3.03          | ((k2_funct_1 @ X38) = (k4_relat_1 @ X38))
% 2.82/3.03          | ~ (v1_funct_1 @ X38)
% 2.82/3.03          | ~ (v1_relat_1 @ X38))),
% 2.82/3.03      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.82/3.03  thf('268', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('269', plain,
% 2.82/3.03      ((((sk_D) != (k4_relat_1 @ sk_C))
% 2.82/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.82/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['267', '268'])).
% 2.82/3.03  thf('270', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.03      inference('demod', [status(thm)], ['184', '185'])).
% 2.82/3.03  thf('271', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('272', plain, ((v2_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('273', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 2.82/3.03      inference('demod', [status(thm)], ['269', '270', '271', '272'])).
% 2.82/3.03  thf('274', plain, ($false),
% 2.82/3.03      inference('simplify_reflect-', [status(thm)], ['266', '273'])).
% 2.82/3.03  
% 2.82/3.03  % SZS output end Refutation
% 2.82/3.03  
% 2.82/3.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
