%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.smldtIT9cF

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:21 EST 2020

% Result     : Theorem 19.62s
% Output     : Refutation 19.62s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 375 expanded)
%              Number of leaves         :   55 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          : 1393 (7104 expanded)
%              Number of equality atoms :   73 ( 104 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( r2_relset_1 @ X58 @ X58 @ ( k1_partfun1 @ X58 @ X59 @ X59 @ X58 @ X57 @ X60 ) @ ( k6_partfun1 @ X58 ) )
      | ( ( k2_relset_1 @ X59 @ X58 @ X60 )
        = X58 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X59 @ X58 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k2_relat_1 @ X49 )
       != X48 )
      | ( v2_funct_2 @ X49 @ X48 )
      | ~ ( v5_relat_1 @ X49 @ X48 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X49: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v5_relat_1 @ X49 @ ( k2_relat_1 @ X49 ) )
      | ( v2_funct_2 @ X49 @ ( k2_relat_1 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['19','22','23','28'])).

thf('30',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( ( k1_partfun1 @ X51 @ X52 @ X54 @ X55 @ X50 @ X53 )
        = ( k5_relat_1 @ X50 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k4_relset_1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( X35 = X38 )
      | ~ ( r2_relset_1 @ X36 @ X37 @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('60',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('61',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','62'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X13 @ X12 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('65',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X13 @ X12 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) )
      | ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','66'])).

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

thf('68',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['68','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('79',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('86',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('87',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('93',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('94',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('96',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('97',plain,(
    ! [X56: $i] :
      ( ( k6_partfun1 @ X56 )
      = ( k6_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('105',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('114',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','105','110','111','112','113'])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['34','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.smldtIT9cF
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.62/19.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.62/19.82  % Solved by: fo/fo7.sh
% 19.62/19.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.62/19.82  % done 24492 iterations in 19.354s
% 19.62/19.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.62/19.82  % SZS output start Refutation
% 19.62/19.82  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 19.62/19.82  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 19.62/19.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.62/19.82  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 19.62/19.82  thf(sk_A_type, type, sk_A: $i).
% 19.62/19.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 19.62/19.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 19.62/19.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 19.62/19.82  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 19.62/19.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 19.62/19.82  thf(sk_C_type, type, sk_C: $i).
% 19.62/19.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.62/19.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 19.62/19.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.62/19.82  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 19.62/19.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.62/19.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.62/19.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.62/19.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 19.62/19.82  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 19.62/19.82  thf(sk_B_type, type, sk_B: $i).
% 19.62/19.82  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 19.62/19.82  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 19.62/19.82  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 19.62/19.82  thf(sk_D_type, type, sk_D: $i).
% 19.62/19.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.62/19.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 19.62/19.82  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 19.62/19.82  thf(t29_funct_2, conjecture,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 19.62/19.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.62/19.82       ( ![D:$i]:
% 19.62/19.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 19.62/19.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 19.62/19.82           ( ( r2_relset_1 @
% 19.62/19.82               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 19.62/19.82               ( k6_partfun1 @ A ) ) =>
% 19.62/19.82             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 19.62/19.82  thf(zf_stmt_0, negated_conjecture,
% 19.62/19.82    (~( ![A:$i,B:$i,C:$i]:
% 19.62/19.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 19.62/19.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.62/19.82          ( ![D:$i]:
% 19.62/19.82            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 19.62/19.82                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 19.62/19.82              ( ( r2_relset_1 @
% 19.62/19.82                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 19.62/19.82                  ( k6_partfun1 @ A ) ) =>
% 19.62/19.82                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 19.62/19.82    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 19.62/19.82  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 19.62/19.82      inference('split', [status(esa)], ['0'])).
% 19.62/19.82  thf('2', plain,
% 19.62/19.82      ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.62/19.82        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 19.62/19.82        (k6_partfun1 @ sk_A))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('3', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(t24_funct_2, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 19.62/19.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.62/19.82       ( ![D:$i]:
% 19.62/19.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 19.62/19.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 19.62/19.82           ( ( r2_relset_1 @
% 19.62/19.82               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 19.62/19.82               ( k6_partfun1 @ B ) ) =>
% 19.62/19.82             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 19.62/19.82  thf('4', plain,
% 19.62/19.82      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 19.62/19.82         (~ (v1_funct_1 @ X57)
% 19.62/19.82          | ~ (v1_funct_2 @ X57 @ X58 @ X59)
% 19.62/19.82          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 19.62/19.82          | ~ (r2_relset_1 @ X58 @ X58 @ 
% 19.62/19.82               (k1_partfun1 @ X58 @ X59 @ X59 @ X58 @ X57 @ X60) @ 
% 19.62/19.82               (k6_partfun1 @ X58))
% 19.62/19.82          | ((k2_relset_1 @ X59 @ X58 @ X60) = (X58))
% 19.62/19.82          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58)))
% 19.62/19.82          | ~ (v1_funct_2 @ X60 @ X59 @ X58)
% 19.62/19.82          | ~ (v1_funct_1 @ X60))),
% 19.62/19.82      inference('cnf', [status(esa)], [t24_funct_2])).
% 19.62/19.82  thf('5', plain,
% 19.62/19.82      (![X0 : $i]:
% 19.62/19.82         (~ (v1_funct_1 @ X0)
% 19.62/19.82          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 19.62/19.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 19.62/19.82          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 19.62/19.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.62/19.82               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 19.62/19.82               (k6_partfun1 @ sk_A))
% 19.62/19.82          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 19.62/19.82          | ~ (v1_funct_1 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['3', '4'])).
% 19.62/19.82  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('8', plain,
% 19.62/19.82      (![X0 : $i]:
% 19.62/19.82         (~ (v1_funct_1 @ X0)
% 19.62/19.82          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 19.62/19.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 19.62/19.82          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 19.62/19.82          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.62/19.82               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 19.62/19.82               (k6_partfun1 @ sk_A)))),
% 19.62/19.82      inference('demod', [status(thm)], ['5', '6', '7'])).
% 19.62/19.82  thf('9', plain,
% 19.62/19.82      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 19.62/19.82        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 19.62/19.82        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 19.62/19.82        | ~ (v1_funct_1 @ sk_D))),
% 19.62/19.82      inference('sup-', [status(thm)], ['2', '8'])).
% 19.62/19.82  thf('10', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(redefinition_k2_relset_1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.62/19.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 19.62/19.82  thf('11', plain,
% 19.62/19.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 19.62/19.82         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 19.62/19.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 19.62/19.82  thf('12', plain,
% 19.62/19.82      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 19.62/19.82      inference('sup-', [status(thm)], ['10', '11'])).
% 19.62/19.82  thf('13', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 19.62/19.82      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 19.62/19.82  thf(d3_funct_2, axiom,
% 19.62/19.82    (![A:$i,B:$i]:
% 19.62/19.82     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 19.62/19.82       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 19.62/19.82  thf('17', plain,
% 19.62/19.82      (![X48 : $i, X49 : $i]:
% 19.62/19.82         (((k2_relat_1 @ X49) != (X48))
% 19.62/19.82          | (v2_funct_2 @ X49 @ X48)
% 19.62/19.82          | ~ (v5_relat_1 @ X49 @ X48)
% 19.62/19.82          | ~ (v1_relat_1 @ X49))),
% 19.62/19.82      inference('cnf', [status(esa)], [d3_funct_2])).
% 19.62/19.82  thf('18', plain,
% 19.62/19.82      (![X49 : $i]:
% 19.62/19.82         (~ (v1_relat_1 @ X49)
% 19.62/19.82          | ~ (v5_relat_1 @ X49 @ (k2_relat_1 @ X49))
% 19.62/19.82          | (v2_funct_2 @ X49 @ (k2_relat_1 @ X49)))),
% 19.62/19.82      inference('simplify', [status(thm)], ['17'])).
% 19.62/19.82  thf('19', plain,
% 19.62/19.82      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 19.62/19.82        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 19.62/19.82        | ~ (v1_relat_1 @ sk_D))),
% 19.62/19.82      inference('sup-', [status(thm)], ['16', '18'])).
% 19.62/19.82  thf('20', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(cc2_relset_1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.62/19.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 19.62/19.82  thf('21', plain,
% 19.62/19.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 19.62/19.82         ((v5_relat_1 @ X14 @ X16)
% 19.62/19.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 19.62/19.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 19.62/19.82  thf('22', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 19.62/19.82      inference('sup-', [status(thm)], ['20', '21'])).
% 19.62/19.82  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 19.62/19.82      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 19.62/19.82  thf('24', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(cc2_relat_1, axiom,
% 19.62/19.82    (![A:$i]:
% 19.62/19.82     ( ( v1_relat_1 @ A ) =>
% 19.62/19.82       ( ![B:$i]:
% 19.62/19.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 19.62/19.82  thf('25', plain,
% 19.62/19.82      (![X7 : $i, X8 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 19.62/19.82          | (v1_relat_1 @ X7)
% 19.62/19.82          | ~ (v1_relat_1 @ X8))),
% 19.62/19.82      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.62/19.82  thf('26', plain,
% 19.62/19.82      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 19.62/19.82      inference('sup-', [status(thm)], ['24', '25'])).
% 19.62/19.82  thf(fc6_relat_1, axiom,
% 19.62/19.82    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 19.62/19.82  thf('27', plain,
% 19.62/19.82      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 19.62/19.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.62/19.82  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 19.62/19.82      inference('demod', [status(thm)], ['26', '27'])).
% 19.62/19.82  thf('29', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 19.62/19.82      inference('demod', [status(thm)], ['19', '22', '23', '28'])).
% 19.62/19.82  thf('30', plain,
% 19.62/19.82      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 19.62/19.82      inference('split', [status(esa)], ['0'])).
% 19.62/19.82  thf('31', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 19.62/19.82      inference('sup-', [status(thm)], ['29', '30'])).
% 19.62/19.82  thf('32', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 19.62/19.82      inference('split', [status(esa)], ['0'])).
% 19.62/19.82  thf('33', plain, (~ ((v2_funct_1 @ sk_C))),
% 19.62/19.82      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 19.62/19.82  thf('34', plain, (~ (v2_funct_1 @ sk_C)),
% 19.62/19.82      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 19.62/19.82  thf('35', plain,
% 19.62/19.82      ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.62/19.82        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 19.62/19.82        (k6_partfun1 @ sk_A))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('36', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('37', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(redefinition_k1_partfun1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.62/19.82     ( ( ( v1_funct_1 @ E ) & 
% 19.62/19.82         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.62/19.82         ( v1_funct_1 @ F ) & 
% 19.62/19.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 19.62/19.82       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 19.62/19.82  thf('38', plain,
% 19.62/19.82      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 19.62/19.82          | ~ (v1_funct_1 @ X50)
% 19.62/19.82          | ~ (v1_funct_1 @ X53)
% 19.62/19.82          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 19.62/19.82          | ((k1_partfun1 @ X51 @ X52 @ X54 @ X55 @ X50 @ X53)
% 19.62/19.82              = (k5_relat_1 @ X50 @ X53)))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 19.62/19.82  thf('39', plain,
% 19.62/19.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.62/19.82         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 19.62/19.82            = (k5_relat_1 @ sk_C @ X0))
% 19.62/19.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.62/19.82          | ~ (v1_funct_1 @ X0)
% 19.62/19.82          | ~ (v1_funct_1 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['37', '38'])).
% 19.62/19.82  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('41', plain,
% 19.62/19.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.62/19.82         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 19.62/19.82            = (k5_relat_1 @ sk_C @ X0))
% 19.62/19.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.62/19.82          | ~ (v1_funct_1 @ X0))),
% 19.62/19.82      inference('demod', [status(thm)], ['39', '40'])).
% 19.62/19.82  thf('42', plain,
% 19.62/19.82      ((~ (v1_funct_1 @ sk_D)
% 19.62/19.82        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 19.62/19.82            = (k5_relat_1 @ sk_C @ sk_D)))),
% 19.62/19.82      inference('sup-', [status(thm)], ['36', '41'])).
% 19.62/19.82  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('44', plain,
% 19.62/19.82      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 19.62/19.82         = (k5_relat_1 @ sk_C @ sk_D))),
% 19.62/19.82      inference('demod', [status(thm)], ['42', '43'])).
% 19.62/19.82  thf('45', plain,
% 19.62/19.82      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 19.62/19.82        (k6_partfun1 @ sk_A))),
% 19.62/19.82      inference('demod', [status(thm)], ['35', '44'])).
% 19.62/19.82  thf('46', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('47', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(dt_k4_relset_1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.62/19.82     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.62/19.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 19.62/19.82       ( m1_subset_1 @
% 19.62/19.82         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 19.62/19.82         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 19.62/19.82  thf('48', plain,
% 19.62/19.82      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 19.62/19.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 19.62/19.82          | (m1_subset_1 @ (k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 19.62/19.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 19.62/19.82      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 19.62/19.82  thf('49', plain,
% 19.62/19.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.62/19.82         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 19.62/19.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 19.62/19.82          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 19.62/19.82      inference('sup-', [status(thm)], ['47', '48'])).
% 19.62/19.82  thf('50', plain,
% 19.62/19.82      ((m1_subset_1 @ 
% 19.62/19.82        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 19.62/19.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.62/19.82      inference('sup-', [status(thm)], ['46', '49'])).
% 19.62/19.82  thf('51', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('52', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(redefinition_k4_relset_1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.62/19.82     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.62/19.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 19.62/19.82       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 19.62/19.82  thf('53', plain,
% 19.62/19.82      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 19.62/19.82          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 19.62/19.82          | ((k4_relset_1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 19.62/19.82              = (k5_relat_1 @ X29 @ X32)))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 19.62/19.82  thf('54', plain,
% 19.62/19.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.62/19.82         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 19.62/19.82            = (k5_relat_1 @ sk_C @ X0))
% 19.62/19.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 19.62/19.82      inference('sup-', [status(thm)], ['52', '53'])).
% 19.62/19.82  thf('55', plain,
% 19.62/19.82      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 19.62/19.82         = (k5_relat_1 @ sk_C @ sk_D))),
% 19.62/19.82      inference('sup-', [status(thm)], ['51', '54'])).
% 19.62/19.82  thf('56', plain,
% 19.62/19.82      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 19.62/19.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.62/19.82      inference('demod', [status(thm)], ['50', '55'])).
% 19.62/19.82  thf(redefinition_r2_relset_1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i,D:$i]:
% 19.62/19.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.62/19.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.62/19.82       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 19.62/19.82  thf('57', plain,
% 19.62/19.82      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 19.62/19.82          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 19.62/19.82          | ((X35) = (X38))
% 19.62/19.82          | ~ (r2_relset_1 @ X36 @ X37 @ X35 @ X38))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 19.62/19.82  thf('58', plain,
% 19.62/19.82      (![X0 : $i]:
% 19.62/19.82         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 19.62/19.82          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 19.62/19.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 19.62/19.82      inference('sup-', [status(thm)], ['56', '57'])).
% 19.62/19.82  thf('59', plain,
% 19.62/19.82      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 19.62/19.82           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 19.62/19.82        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 19.62/19.82      inference('sup-', [status(thm)], ['45', '58'])).
% 19.62/19.82  thf(t29_relset_1, axiom,
% 19.62/19.82    (![A:$i]:
% 19.62/19.82     ( m1_subset_1 @
% 19.62/19.82       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 19.62/19.82  thf('60', plain,
% 19.62/19.82      (![X39 : $i]:
% 19.62/19.82         (m1_subset_1 @ (k6_relat_1 @ X39) @ 
% 19.62/19.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 19.62/19.82      inference('cnf', [status(esa)], [t29_relset_1])).
% 19.62/19.82  thf(redefinition_k6_partfun1, axiom,
% 19.62/19.82    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 19.62/19.82  thf('61', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 19.62/19.82  thf('62', plain,
% 19.62/19.82      (![X39 : $i]:
% 19.62/19.82         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 19.62/19.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 19.62/19.82      inference('demod', [status(thm)], ['60', '61'])).
% 19.62/19.82  thf('63', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 19.62/19.82      inference('demod', [status(thm)], ['59', '62'])).
% 19.62/19.82  thf(t53_funct_1, axiom,
% 19.62/19.82    (![A:$i]:
% 19.62/19.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.62/19.82       ( ( ?[B:$i]:
% 19.62/19.82           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 19.62/19.82             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 19.62/19.82         ( v2_funct_1 @ A ) ) ))).
% 19.62/19.82  thf('64', plain,
% 19.62/19.82      (![X12 : $i, X13 : $i]:
% 19.62/19.82         (~ (v1_relat_1 @ X12)
% 19.62/19.82          | ~ (v1_funct_1 @ X12)
% 19.62/19.82          | ((k5_relat_1 @ X13 @ X12) != (k6_relat_1 @ (k1_relat_1 @ X13)))
% 19.62/19.82          | (v2_funct_1 @ X13)
% 19.62/19.82          | ~ (v1_funct_1 @ X13)
% 19.62/19.82          | ~ (v1_relat_1 @ X13))),
% 19.62/19.82      inference('cnf', [status(esa)], [t53_funct_1])).
% 19.62/19.82  thf('65', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 19.62/19.82  thf('66', plain,
% 19.62/19.82      (![X12 : $i, X13 : $i]:
% 19.62/19.82         (~ (v1_relat_1 @ X12)
% 19.62/19.82          | ~ (v1_funct_1 @ X12)
% 19.62/19.82          | ((k5_relat_1 @ X13 @ X12) != (k6_partfun1 @ (k1_relat_1 @ X13)))
% 19.62/19.82          | (v2_funct_1 @ X13)
% 19.62/19.82          | ~ (v1_funct_1 @ X13)
% 19.62/19.82          | ~ (v1_relat_1 @ X13))),
% 19.62/19.82      inference('demod', [status(thm)], ['64', '65'])).
% 19.62/19.82  thf('67', plain,
% 19.62/19.82      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 19.62/19.82        | ~ (v1_relat_1 @ sk_C)
% 19.62/19.82        | ~ (v1_funct_1 @ sk_C)
% 19.62/19.82        | (v2_funct_1 @ sk_C)
% 19.62/19.82        | ~ (v1_funct_1 @ sk_D)
% 19.62/19.82        | ~ (v1_relat_1 @ sk_D))),
% 19.62/19.82      inference('sup-', [status(thm)], ['63', '66'])).
% 19.62/19.82  thf(d1_funct_2, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.62/19.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.62/19.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 19.62/19.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 19.62/19.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.62/19.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 19.62/19.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 19.62/19.82  thf(zf_stmt_1, axiom,
% 19.62/19.82    (![B:$i,A:$i]:
% 19.62/19.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.62/19.82       ( zip_tseitin_0 @ B @ A ) ))).
% 19.62/19.82  thf('68', plain,
% 19.62/19.82      (![X40 : $i, X41 : $i]:
% 19.62/19.82         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.62/19.82  thf(t113_zfmisc_1, axiom,
% 19.62/19.82    (![A:$i,B:$i]:
% 19.62/19.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 19.62/19.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 19.62/19.82  thf('69', plain,
% 19.62/19.82      (![X3 : $i, X4 : $i]:
% 19.62/19.82         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 19.62/19.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 19.62/19.82  thf('70', plain,
% 19.62/19.82      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 19.62/19.82      inference('simplify', [status(thm)], ['69'])).
% 19.62/19.82  thf('71', plain,
% 19.62/19.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.62/19.82         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 19.62/19.82      inference('sup+', [status(thm)], ['68', '70'])).
% 19.62/19.82  thf('72', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(cc1_subset_1, axiom,
% 19.62/19.82    (![A:$i]:
% 19.62/19.82     ( ( v1_xboole_0 @ A ) =>
% 19.62/19.82       ( ![B:$i]:
% 19.62/19.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 19.62/19.82  thf('73', plain,
% 19.62/19.82      (![X5 : $i, X6 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 19.62/19.82          | (v1_xboole_0 @ X5)
% 19.62/19.82          | ~ (v1_xboole_0 @ X6))),
% 19.62/19.82      inference('cnf', [status(esa)], [cc1_subset_1])).
% 19.62/19.82  thf('74', plain,
% 19.62/19.82      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['72', '73'])).
% 19.62/19.82  thf('75', plain,
% 19.62/19.82      (![X0 : $i]:
% 19.62/19.82         (~ (v1_xboole_0 @ k1_xboole_0)
% 19.62/19.82          | (zip_tseitin_0 @ sk_B @ X0)
% 19.62/19.82          | (v1_xboole_0 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['71', '74'])).
% 19.62/19.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 19.62/19.82  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.62/19.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.62/19.82  thf('77', plain,
% 19.62/19.82      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 19.62/19.82      inference('demod', [status(thm)], ['75', '76'])).
% 19.62/19.82  thf('78', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 19.62/19.82  thf(zf_stmt_3, axiom,
% 19.62/19.82    (![C:$i,B:$i,A:$i]:
% 19.62/19.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 19.62/19.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 19.62/19.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 19.62/19.82  thf(zf_stmt_5, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.62/19.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 19.62/19.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.62/19.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 19.62/19.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 19.62/19.82  thf('79', plain,
% 19.62/19.82      (![X45 : $i, X46 : $i, X47 : $i]:
% 19.62/19.82         (~ (zip_tseitin_0 @ X45 @ X46)
% 19.62/19.82          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 19.62/19.82          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.62/19.82  thf('80', plain,
% 19.62/19.82      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 19.62/19.82      inference('sup-', [status(thm)], ['78', '79'])).
% 19.62/19.82  thf('81', plain,
% 19.62/19.82      (((v1_xboole_0 @ sk_C) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 19.62/19.82      inference('sup-', [status(thm)], ['77', '80'])).
% 19.62/19.82  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('83', plain,
% 19.62/19.82      (![X42 : $i, X43 : $i, X44 : $i]:
% 19.62/19.82         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 19.62/19.82          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 19.62/19.82          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.62/19.82  thf('84', plain,
% 19.62/19.82      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 19.62/19.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 19.62/19.82      inference('sup-', [status(thm)], ['82', '83'])).
% 19.62/19.82  thf('85', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf(redefinition_k1_relset_1, axiom,
% 19.62/19.82    (![A:$i,B:$i,C:$i]:
% 19.62/19.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.62/19.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 19.62/19.82  thf('86', plain,
% 19.62/19.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 19.62/19.82         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 19.62/19.82          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.62/19.82  thf('87', plain,
% 19.62/19.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['85', '86'])).
% 19.62/19.82  thf('88', plain,
% 19.62/19.82      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 19.62/19.82      inference('demod', [status(thm)], ['84', '87'])).
% 19.62/19.82  thf('89', plain, (((v1_xboole_0 @ sk_C) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 19.62/19.82      inference('sup-', [status(thm)], ['81', '88'])).
% 19.62/19.82  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 19.62/19.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 19.62/19.82  thf(t8_boole, axiom,
% 19.62/19.82    (![A:$i,B:$i]:
% 19.62/19.82     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 19.62/19.82  thf('91', plain,
% 19.62/19.82      (![X0 : $i, X1 : $i]:
% 19.62/19.82         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 19.62/19.82      inference('cnf', [status(esa)], [t8_boole])).
% 19.62/19.82  thf('92', plain,
% 19.62/19.82      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 19.62/19.82      inference('sup-', [status(thm)], ['90', '91'])).
% 19.62/19.82  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 19.62/19.82  thf('93', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.62/19.82      inference('cnf', [status(esa)], [t81_relat_1])).
% 19.62/19.82  thf('94', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 19.62/19.82  thf('95', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.62/19.82      inference('demod', [status(thm)], ['93', '94'])).
% 19.62/19.82  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 19.62/19.82  thf('96', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 19.62/19.82      inference('cnf', [status(esa)], [t52_funct_1])).
% 19.62/19.82  thf('97', plain, (![X56 : $i]: ((k6_partfun1 @ X56) = (k6_relat_1 @ X56))),
% 19.62/19.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 19.62/19.82  thf('98', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 19.62/19.82      inference('demod', [status(thm)], ['96', '97'])).
% 19.62/19.82  thf('99', plain, ((v2_funct_1 @ k1_xboole_0)),
% 19.62/19.82      inference('sup+', [status(thm)], ['95', '98'])).
% 19.62/19.82  thf('100', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 19.62/19.82      inference('sup+', [status(thm)], ['92', '99'])).
% 19.62/19.82  thf('101', plain, ((((sk_A) = (k1_relat_1 @ sk_C)) | (v2_funct_1 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['89', '100'])).
% 19.62/19.82  thf('102', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 19.62/19.82      inference('split', [status(esa)], ['0'])).
% 19.62/19.82  thf('103', plain,
% 19.62/19.82      ((((sk_A) = (k1_relat_1 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 19.62/19.82      inference('sup-', [status(thm)], ['101', '102'])).
% 19.62/19.82  thf('104', plain, (~ ((v2_funct_1 @ sk_C))),
% 19.62/19.82      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 19.62/19.82  thf('105', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 19.62/19.82      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 19.62/19.82  thf('106', plain,
% 19.62/19.82      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('107', plain,
% 19.62/19.82      (![X7 : $i, X8 : $i]:
% 19.62/19.82         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 19.62/19.82          | (v1_relat_1 @ X7)
% 19.62/19.82          | ~ (v1_relat_1 @ X8))),
% 19.62/19.82      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.62/19.82  thf('108', plain,
% 19.62/19.82      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 19.62/19.82      inference('sup-', [status(thm)], ['106', '107'])).
% 19.62/19.82  thf('109', plain,
% 19.62/19.82      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 19.62/19.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.62/19.82  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 19.62/19.82      inference('demod', [status(thm)], ['108', '109'])).
% 19.62/19.82  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('112', plain, ((v1_funct_1 @ sk_D)),
% 19.62/19.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.62/19.82  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 19.62/19.82      inference('demod', [status(thm)], ['26', '27'])).
% 19.62/19.82  thf('114', plain,
% 19.62/19.82      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)) | (v2_funct_1 @ sk_C))),
% 19.62/19.82      inference('demod', [status(thm)],
% 19.62/19.82                ['67', '105', '110', '111', '112', '113'])).
% 19.62/19.82  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 19.62/19.82      inference('simplify', [status(thm)], ['114'])).
% 19.62/19.82  thf('116', plain, ($false), inference('demod', [status(thm)], ['34', '115'])).
% 19.62/19.82  
% 19.62/19.82  % SZS output end Refutation
% 19.62/19.82  
% 19.68/19.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
