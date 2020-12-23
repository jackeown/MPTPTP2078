%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PQSdAdsqtu

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:08 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 309 expanded)
%              Number of leaves         :   41 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          : 1215 (5684 expanded)
%              Number of equality atoms :   48 (  87 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['13'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('16',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','16'])).

thf('18',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('38',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37 ) )
      | ( v2_funct_1 @ X41 )
      | ( X39 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X38 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['19','56'])).

thf('58',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_partfun1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('64',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_relat_1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['70','74','77','78','79','80'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('83',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['70','74','77','78','79','80'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['84','87','88','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['60','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PQSdAdsqtu
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.73/2.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.73/2.95  % Solved by: fo/fo7.sh
% 2.73/2.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.95  % done 3326 iterations in 2.496s
% 2.73/2.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.73/2.95  % SZS output start Refutation
% 2.73/2.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.73/2.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.73/2.95  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.73/2.95  thf(sk_C_type, type, sk_C: $i).
% 2.73/2.95  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.73/2.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.73/2.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.73/2.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.73/2.95  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.73/2.95  thf(sk_B_type, type, sk_B: $i).
% 2.73/2.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.73/2.95  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.73/2.95  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.95  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.73/2.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.73/2.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.73/2.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.73/2.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.73/2.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.95  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.95  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.73/2.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.73/2.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.73/2.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.73/2.95  thf(t29_funct_2, conjecture,
% 2.73/2.95    (![A:$i,B:$i,C:$i]:
% 2.73/2.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.95       ( ![D:$i]:
% 2.73/2.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.95           ( ( r2_relset_1 @
% 2.73/2.95               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.95               ( k6_partfun1 @ A ) ) =>
% 2.73/2.95             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.73/2.95  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.95    (~( ![A:$i,B:$i,C:$i]:
% 2.73/2.95        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.95          ( ![D:$i]:
% 2.73/2.95            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.95              ( ( r2_relset_1 @
% 2.73/2.95                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.95                  ( k6_partfun1 @ A ) ) =>
% 2.73/2.95                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.73/2.95    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.73/2.95  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('1', plain,
% 2.73/2.95      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.73/2.95      inference('split', [status(esa)], ['0'])).
% 2.73/2.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.73/2.95  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.73/2.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.73/2.95  thf(t8_boole, axiom,
% 2.73/2.95    (![A:$i,B:$i]:
% 2.73/2.95     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.73/2.95  thf('3', plain,
% 2.73/2.95      (![X0 : $i, X1 : $i]:
% 2.73/2.95         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.73/2.95      inference('cnf', [status(esa)], [t8_boole])).
% 2.73/2.95  thf('4', plain,
% 2.73/2.95      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.73/2.95      inference('sup-', [status(thm)], ['2', '3'])).
% 2.73/2.95  thf(t71_relat_1, axiom,
% 2.73/2.95    (![A:$i]:
% 2.73/2.95     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.73/2.95       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.73/2.95  thf('5', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 2.73/2.95      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.73/2.95  thf(t64_relat_1, axiom,
% 2.73/2.95    (![A:$i]:
% 2.73/2.95     ( ( v1_relat_1 @ A ) =>
% 2.73/2.95       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.73/2.95           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.73/2.95         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.73/2.95  thf('6', plain,
% 2.73/2.95      (![X2 : $i]:
% 2.73/2.95         (((k2_relat_1 @ X2) != (k1_xboole_0))
% 2.73/2.95          | ((X2) = (k1_xboole_0))
% 2.73/2.95          | ~ (v1_relat_1 @ X2))),
% 2.73/2.95      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.73/2.95  thf('7', plain,
% 2.73/2.95      (![X0 : $i]:
% 2.73/2.95         (((X0) != (k1_xboole_0))
% 2.73/2.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.73/2.95          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 2.73/2.95      inference('sup-', [status(thm)], ['5', '6'])).
% 2.73/2.95  thf(dt_k6_partfun1, axiom,
% 2.73/2.95    (![A:$i]:
% 2.73/2.95     ( ( m1_subset_1 @
% 2.73/2.95         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.73/2.95       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.73/2.95  thf('8', plain,
% 2.73/2.95      (![X31 : $i]:
% 2.73/2.95         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 2.73/2.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.73/2.95      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.73/2.95  thf(redefinition_k6_partfun1, axiom,
% 2.73/2.95    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.73/2.95  thf('9', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.73/2.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.95  thf('10', plain,
% 2.73/2.95      (![X31 : $i]:
% 2.73/2.95         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.73/2.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.73/2.95      inference('demod', [status(thm)], ['8', '9'])).
% 2.73/2.95  thf(cc1_relset_1, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i]:
% 2.73/2.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.95       ( v1_relat_1 @ C ) ))).
% 2.73/2.95  thf('11', plain,
% 2.73/2.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.73/2.95         ((v1_relat_1 @ X6)
% 2.73/2.95          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.73/2.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.73/2.95  thf('12', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 2.73/2.95      inference('sup-', [status(thm)], ['10', '11'])).
% 2.73/2.95  thf('13', plain,
% 2.73/2.95      (![X0 : $i]:
% 2.73/2.95         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 2.73/2.95      inference('demod', [status(thm)], ['7', '12'])).
% 2.73/2.95  thf('14', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.73/2.95      inference('simplify', [status(thm)], ['13'])).
% 2.73/2.95  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.73/2.95  thf('15', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.73/2.95      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.73/2.95  thf('16', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.73/2.95      inference('sup+', [status(thm)], ['14', '15'])).
% 2.73/2.95  thf('17', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.73/2.95      inference('sup+', [status(thm)], ['4', '16'])).
% 2.73/2.95  thf('18', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.95      inference('split', [status(esa)], ['0'])).
% 2.73/2.95  thf('19', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.95      inference('sup-', [status(thm)], ['17', '18'])).
% 2.73/2.95  thf('20', plain,
% 2.73/2.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.95        (k6_partfun1 @ sk_A))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('21', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.73/2.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.95  thf('22', plain,
% 2.73/2.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.95        (k6_relat_1 @ sk_A))),
% 2.73/2.95      inference('demod', [status(thm)], ['20', '21'])).
% 2.73/2.95  thf('23', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('24', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf(dt_k1_partfun1, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.95     ( ( ( v1_funct_1 @ E ) & 
% 2.73/2.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.95         ( v1_funct_1 @ F ) & 
% 2.73/2.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.95       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.73/2.95         ( m1_subset_1 @
% 2.73/2.95           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.73/2.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.73/2.95  thf('25', plain,
% 2.73/2.95      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.73/2.95         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.73/2.95          | ~ (v1_funct_1 @ X24)
% 2.73/2.95          | ~ (v1_funct_1 @ X27)
% 2.73/2.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.73/2.95          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 2.73/2.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 2.73/2.95      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.73/2.95  thf('26', plain,
% 2.73/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.73/2.95          | ~ (v1_funct_1 @ X1)
% 2.73/2.95          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.95      inference('sup-', [status(thm)], ['24', '25'])).
% 2.73/2.95  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('28', plain,
% 2.73/2.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.73/2.95          | ~ (v1_funct_1 @ X1))),
% 2.73/2.95      inference('demod', [status(thm)], ['26', '27'])).
% 2.73/2.95  thf('29', plain,
% 2.73/2.95      ((~ (v1_funct_1 @ sk_D)
% 2.73/2.95        | (m1_subset_1 @ 
% 2.73/2.95           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.95      inference('sup-', [status(thm)], ['23', '28'])).
% 2.73/2.95  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('31', plain,
% 2.73/2.95      ((m1_subset_1 @ 
% 2.73/2.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.73/2.95      inference('demod', [status(thm)], ['29', '30'])).
% 2.73/2.95  thf(redefinition_r2_relset_1, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.95     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.95       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.73/2.95  thf('32', plain,
% 2.73/2.95      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.95         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.73/2.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.73/2.95          | ((X18) = (X21))
% 2.73/2.95          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.73/2.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.73/2.95  thf('33', plain,
% 2.73/2.95      (![X0 : $i]:
% 2.73/2.95         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.95             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.73/2.95          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.73/2.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.95      inference('sup-', [status(thm)], ['31', '32'])).
% 2.73/2.95  thf('34', plain,
% 2.73/2.95      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.73/2.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.73/2.95        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.95            = (k6_relat_1 @ sk_A)))),
% 2.73/2.95      inference('sup-', [status(thm)], ['22', '33'])).
% 2.73/2.95  thf('35', plain,
% 2.73/2.95      (![X31 : $i]:
% 2.73/2.95         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.73/2.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.73/2.95      inference('demod', [status(thm)], ['8', '9'])).
% 2.73/2.95  thf('36', plain,
% 2.73/2.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.95         = (k6_relat_1 @ sk_A))),
% 2.73/2.95      inference('demod', [status(thm)], ['34', '35'])).
% 2.73/2.95  thf('37', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf(t26_funct_2, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.73/2.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.95       ( ![E:$i]:
% 2.73/2.95         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.73/2.95             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.73/2.95           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.73/2.95             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.73/2.95               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.73/2.95  thf('38', plain,
% 2.73/2.95      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X37)
% 2.73/2.95          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.73/2.95          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.73/2.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 2.73/2.95          | (v2_funct_1 @ X41)
% 2.73/2.95          | ((X39) = (k1_xboole_0))
% 2.73/2.95          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 2.73/2.95          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 2.73/2.95          | ~ (v1_funct_1 @ X41))),
% 2.73/2.95      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.73/2.95  thf('39', plain,
% 2.73/2.95      (![X0 : $i, X1 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X0)
% 2.73/2.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.73/2.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.73/2.95          | ((sk_A) = (k1_xboole_0))
% 2.73/2.95          | (v2_funct_1 @ X0)
% 2.73/2.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.73/2.95          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.95          | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.95      inference('sup-', [status(thm)], ['37', '38'])).
% 2.73/2.95  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('42', plain,
% 2.73/2.95      (![X0 : $i, X1 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X0)
% 2.73/2.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.73/2.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.73/2.95          | ((sk_A) = (k1_xboole_0))
% 2.73/2.95          | (v2_funct_1 @ X0)
% 2.73/2.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.73/2.95      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.73/2.95  thf('43', plain,
% 2.73/2.95      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.73/2.95        | (v2_funct_1 @ sk_C)
% 2.73/2.95        | ((sk_A) = (k1_xboole_0))
% 2.73/2.95        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.73/2.95        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.95        | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.95      inference('sup-', [status(thm)], ['36', '42'])).
% 2.73/2.95  thf('44', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.73/2.95      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.73/2.95  thf('45', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('46', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('48', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.95      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 2.73/2.95  thf('49', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.95      inference('split', [status(esa)], ['0'])).
% 2.73/2.95  thf('50', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.95      inference('sup-', [status(thm)], ['48', '49'])).
% 2.73/2.95  thf('51', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf(cc3_relset_1, axiom,
% 2.73/2.95    (![A:$i,B:$i]:
% 2.73/2.95     ( ( v1_xboole_0 @ A ) =>
% 2.73/2.95       ( ![C:$i]:
% 2.73/2.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.95           ( v1_xboole_0 @ C ) ) ) ))).
% 2.73/2.95  thf('52', plain,
% 2.73/2.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.73/2.95         (~ (v1_xboole_0 @ X12)
% 2.73/2.95          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 2.73/2.95          | (v1_xboole_0 @ X13))),
% 2.73/2.95      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.73/2.95  thf('53', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.73/2.95      inference('sup-', [status(thm)], ['51', '52'])).
% 2.73/2.95  thf('54', plain,
% 2.73/2.95      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 2.73/2.95         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.95      inference('sup-', [status(thm)], ['50', '53'])).
% 2.73/2.95  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.73/2.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.73/2.95  thf('56', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.95      inference('demod', [status(thm)], ['54', '55'])).
% 2.73/2.95  thf('57', plain, (((v2_funct_1 @ sk_C))),
% 2.73/2.95      inference('demod', [status(thm)], ['19', '56'])).
% 2.73/2.95  thf('58', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 2.73/2.95      inference('split', [status(esa)], ['0'])).
% 2.73/2.95  thf('59', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.73/2.95      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 2.73/2.95  thf('60', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 2.73/2.95      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 2.73/2.95  thf('61', plain,
% 2.73/2.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.95         = (k6_relat_1 @ sk_A))),
% 2.73/2.95      inference('demod', [status(thm)], ['34', '35'])).
% 2.73/2.95  thf('62', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf(t24_funct_2, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i]:
% 2.73/2.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.95       ( ![D:$i]:
% 2.73/2.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.95           ( ( r2_relset_1 @
% 2.73/2.95               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.73/2.95               ( k6_partfun1 @ B ) ) =>
% 2.73/2.95             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.73/2.95  thf('63', plain,
% 2.73/2.95      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X33)
% 2.73/2.95          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.73/2.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.73/2.95          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.73/2.95               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.73/2.95               (k6_partfun1 @ X34))
% 2.73/2.95          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.73/2.95          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.73/2.95          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.73/2.95          | ~ (v1_funct_1 @ X36))),
% 2.73/2.95      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.73/2.95  thf('64', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.73/2.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.95  thf('65', plain,
% 2.73/2.95      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X33)
% 2.73/2.95          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.73/2.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.73/2.95          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.73/2.95               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.73/2.95               (k6_relat_1 @ X34))
% 2.73/2.95          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.73/2.95          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.73/2.95          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.73/2.95          | ~ (v1_funct_1 @ X36))),
% 2.73/2.95      inference('demod', [status(thm)], ['63', '64'])).
% 2.73/2.95  thf('66', plain,
% 2.73/2.95      (![X0 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X0)
% 2.73/2.95          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.73/2.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.95          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.73/2.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.95               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.73/2.95               (k6_relat_1 @ sk_A))
% 2.73/2.95          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.95          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.95      inference('sup-', [status(thm)], ['62', '65'])).
% 2.73/2.95  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('69', plain,
% 2.73/2.95      (![X0 : $i]:
% 2.73/2.95         (~ (v1_funct_1 @ X0)
% 2.73/2.95          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.73/2.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.95          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.73/2.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.95               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.73/2.95               (k6_relat_1 @ sk_A)))),
% 2.73/2.95      inference('demod', [status(thm)], ['66', '67', '68'])).
% 2.73/2.95  thf('70', plain,
% 2.73/2.95      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 2.73/2.95           (k6_relat_1 @ sk_A))
% 2.73/2.95        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.73/2.95        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.95        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.95        | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.95      inference('sup-', [status(thm)], ['61', '69'])).
% 2.73/2.95  thf('71', plain,
% 2.73/2.95      (![X31 : $i]:
% 2.73/2.95         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.73/2.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.73/2.95      inference('demod', [status(thm)], ['8', '9'])).
% 2.73/2.95  thf('72', plain,
% 2.73/2.95      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.95         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.73/2.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.73/2.95          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 2.73/2.95          | ((X18) != (X21)))),
% 2.73/2.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.73/2.95  thf('73', plain,
% 2.73/2.95      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.95         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 2.73/2.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.73/2.95      inference('simplify', [status(thm)], ['72'])).
% 2.73/2.95  thf('74', plain,
% 2.73/2.95      (![X0 : $i]:
% 2.73/2.95         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.73/2.95      inference('sup-', [status(thm)], ['71', '73'])).
% 2.73/2.95  thf('75', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf(redefinition_k2_relset_1, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i]:
% 2.73/2.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.73/2.95  thf('76', plain,
% 2.73/2.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.73/2.95         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.73/2.95          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.73/2.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.73/2.95  thf('77', plain,
% 2.73/2.95      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.73/2.95      inference('sup-', [status(thm)], ['75', '76'])).
% 2.73/2.95  thf('78', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.95      inference('demod', [status(thm)], ['70', '74', '77', '78', '79', '80'])).
% 2.73/2.95  thf(d3_funct_2, axiom,
% 2.73/2.95    (![A:$i,B:$i]:
% 2.73/2.95     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.73/2.95       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.73/2.95  thf('82', plain,
% 2.73/2.95      (![X22 : $i, X23 : $i]:
% 2.73/2.95         (((k2_relat_1 @ X23) != (X22))
% 2.73/2.95          | (v2_funct_2 @ X23 @ X22)
% 2.73/2.95          | ~ (v5_relat_1 @ X23 @ X22)
% 2.73/2.95          | ~ (v1_relat_1 @ X23))),
% 2.73/2.95      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.73/2.95  thf('83', plain,
% 2.73/2.95      (![X23 : $i]:
% 2.73/2.95         (~ (v1_relat_1 @ X23)
% 2.73/2.95          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 2.73/2.95          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 2.73/2.95      inference('simplify', [status(thm)], ['82'])).
% 2.73/2.95  thf('84', plain,
% 2.73/2.95      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.73/2.95        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.73/2.95        | ~ (v1_relat_1 @ sk_D))),
% 2.73/2.95      inference('sup-', [status(thm)], ['81', '83'])).
% 2.73/2.95  thf('85', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf(cc2_relset_1, axiom,
% 2.73/2.95    (![A:$i,B:$i,C:$i]:
% 2.73/2.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.73/2.95  thf('86', plain,
% 2.73/2.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.73/2.95         ((v5_relat_1 @ X9 @ X11)
% 2.73/2.95          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.73/2.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.73/2.95  thf('87', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.73/2.95      inference('sup-', [status(thm)], ['85', '86'])).
% 2.73/2.95  thf('88', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.95      inference('demod', [status(thm)], ['70', '74', '77', '78', '79', '80'])).
% 2.73/2.95  thf('89', plain,
% 2.73/2.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.95  thf('90', plain,
% 2.73/2.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.73/2.95         ((v1_relat_1 @ X6)
% 2.73/2.95          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.73/2.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.73/2.95  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.95      inference('sup-', [status(thm)], ['89', '90'])).
% 2.73/2.95  thf('92', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.73/2.95      inference('demod', [status(thm)], ['84', '87', '88', '91'])).
% 2.73/2.95  thf('93', plain, ($false), inference('demod', [status(thm)], ['60', '92'])).
% 2.73/2.95  
% 2.73/2.95  % SZS output end Refutation
% 2.73/2.95  
% 2.73/2.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
