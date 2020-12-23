%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tVkCgrVJsV

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:21 EST 2020

% Result     : Theorem 4.40s
% Output     : Refutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 315 expanded)
%              Number of leaves         :   47 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          : 1189 (5177 expanded)
%              Number of equality atoms :   44 (  75 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('26',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('27',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47 ) )
      | ( v2_funct_1 @ X51 )
      | ( X49 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X48 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['12','56'])).

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

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('70',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('75',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('76',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('81',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('90',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['85','86'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['74','77','88','89','90','91','96'])).

thf('98',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('99',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('101',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('102',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['97','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['85','86'])).

thf('107',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['60','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tVkCgrVJsV
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.40/4.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.40/4.58  % Solved by: fo/fo7.sh
% 4.40/4.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.40/4.58  % done 4241 iterations in 4.120s
% 4.40/4.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.40/4.58  % SZS output start Refutation
% 4.40/4.58  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.40/4.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.40/4.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.40/4.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.40/4.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.40/4.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.40/4.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.40/4.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.40/4.58  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.40/4.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.40/4.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.40/4.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.40/4.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.40/4.58  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.40/4.58  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.40/4.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.40/4.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.40/4.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.40/4.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.40/4.58  thf(sk_C_type, type, sk_C: $i).
% 4.40/4.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.40/4.58  thf(sk_B_type, type, sk_B: $i).
% 4.40/4.58  thf(sk_D_type, type, sk_D: $i).
% 4.40/4.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.40/4.58  thf(sk_A_type, type, sk_A: $i).
% 4.40/4.58  thf(t29_funct_2, conjecture,
% 4.40/4.58    (![A:$i,B:$i,C:$i]:
% 4.40/4.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.40/4.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.40/4.58       ( ![D:$i]:
% 4.40/4.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.40/4.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.40/4.58           ( ( r2_relset_1 @
% 4.40/4.58               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.40/4.58               ( k6_partfun1 @ A ) ) =>
% 4.40/4.58             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.40/4.58  thf(zf_stmt_0, negated_conjecture,
% 4.40/4.58    (~( ![A:$i,B:$i,C:$i]:
% 4.40/4.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.40/4.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.40/4.58          ( ![D:$i]:
% 4.40/4.58            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.40/4.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.40/4.58              ( ( r2_relset_1 @
% 4.40/4.58                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.40/4.58                  ( k6_partfun1 @ A ) ) =>
% 4.40/4.58                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.40/4.58    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.40/4.58  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('1', plain,
% 4.40/4.58      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.40/4.58      inference('split', [status(esa)], ['0'])).
% 4.40/4.58  thf(l13_xboole_0, axiom,
% 4.40/4.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.40/4.58  thf('2', plain,
% 4.40/4.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.40/4.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.40/4.58  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.40/4.58  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.40/4.58      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.40/4.58  thf(redefinition_k6_partfun1, axiom,
% 4.40/4.58    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.40/4.58  thf('4', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.40/4.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.40/4.58  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.40/4.58      inference('demod', [status(thm)], ['3', '4'])).
% 4.40/4.58  thf(fc4_funct_1, axiom,
% 4.40/4.58    (![A:$i]:
% 4.40/4.58     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.40/4.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.40/4.58  thf('6', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 4.40/4.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.40/4.58  thf('7', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.40/4.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.40/4.58  thf('8', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 4.40/4.58      inference('demod', [status(thm)], ['6', '7'])).
% 4.40/4.58  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.40/4.58      inference('sup+', [status(thm)], ['5', '8'])).
% 4.40/4.58  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.40/4.58      inference('sup+', [status(thm)], ['2', '9'])).
% 4.40/4.58  thf('11', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.40/4.58      inference('split', [status(esa)], ['0'])).
% 4.40/4.58  thf('12', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.40/4.58      inference('sup-', [status(thm)], ['10', '11'])).
% 4.40/4.58  thf('13', plain,
% 4.40/4.58      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.40/4.58        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.40/4.58        (k6_partfun1 @ sk_A))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('14', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('15', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf(dt_k1_partfun1, axiom,
% 4.40/4.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.40/4.58     ( ( ( v1_funct_1 @ E ) & 
% 4.40/4.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.40/4.58         ( v1_funct_1 @ F ) & 
% 4.40/4.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.40/4.58       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.40/4.58         ( m1_subset_1 @
% 4.40/4.58           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.40/4.58           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.40/4.58  thf('16', plain,
% 4.40/4.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.40/4.58         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.40/4.58          | ~ (v1_funct_1 @ X34)
% 4.40/4.58          | ~ (v1_funct_1 @ X37)
% 4.40/4.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.40/4.58          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 4.40/4.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 4.40/4.58      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.40/4.58  thf('17', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.40/4.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.40/4.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.40/4.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.40/4.58          | ~ (v1_funct_1 @ X1)
% 4.40/4.58          | ~ (v1_funct_1 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['15', '16'])).
% 4.40/4.58  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('19', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.40/4.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.40/4.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.40/4.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.40/4.58          | ~ (v1_funct_1 @ X1))),
% 4.40/4.58      inference('demod', [status(thm)], ['17', '18'])).
% 4.40/4.58  thf('20', plain,
% 4.40/4.58      ((~ (v1_funct_1 @ sk_D)
% 4.40/4.58        | (m1_subset_1 @ 
% 4.40/4.58           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.40/4.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.40/4.58      inference('sup-', [status(thm)], ['14', '19'])).
% 4.40/4.58  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('22', plain,
% 4.40/4.58      ((m1_subset_1 @ 
% 4.40/4.58        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.40/4.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.40/4.58      inference('demod', [status(thm)], ['20', '21'])).
% 4.40/4.58  thf(redefinition_r2_relset_1, axiom,
% 4.40/4.58    (![A:$i,B:$i,C:$i,D:$i]:
% 4.40/4.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.40/4.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.40/4.58       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.40/4.58  thf('23', plain,
% 4.40/4.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.40/4.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.40/4.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.40/4.58          | ((X27) = (X30))
% 4.40/4.58          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 4.40/4.58      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.40/4.58  thf('24', plain,
% 4.40/4.58      (![X0 : $i]:
% 4.40/4.58         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.40/4.58             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 4.40/4.58          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 4.40/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.40/4.58      inference('sup-', [status(thm)], ['22', '23'])).
% 4.40/4.58  thf('25', plain,
% 4.40/4.58      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.40/4.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.40/4.58        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.40/4.58            = (k6_partfun1 @ sk_A)))),
% 4.40/4.58      inference('sup-', [status(thm)], ['13', '24'])).
% 4.40/4.58  thf(t29_relset_1, axiom,
% 4.40/4.58    (![A:$i]:
% 4.40/4.58     ( m1_subset_1 @
% 4.40/4.58       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.40/4.58  thf('26', plain,
% 4.40/4.58      (![X31 : $i]:
% 4.40/4.58         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 4.40/4.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.40/4.58      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.40/4.58  thf('27', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.40/4.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.40/4.58  thf('28', plain,
% 4.40/4.58      (![X31 : $i]:
% 4.40/4.58         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.40/4.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.40/4.58      inference('demod', [status(thm)], ['26', '27'])).
% 4.40/4.58  thf('29', plain,
% 4.40/4.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.40/4.58         = (k6_partfun1 @ sk_A))),
% 4.40/4.58      inference('demod', [status(thm)], ['25', '28'])).
% 4.40/4.58  thf('30', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf(t26_funct_2, axiom,
% 4.40/4.58    (![A:$i,B:$i,C:$i,D:$i]:
% 4.40/4.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.40/4.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.40/4.58       ( ![E:$i]:
% 4.40/4.58         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.40/4.58             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.40/4.58           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.40/4.58             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.40/4.58               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.40/4.58  thf('31', plain,
% 4.40/4.58      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 4.40/4.58         (~ (v1_funct_1 @ X47)
% 4.40/4.58          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 4.40/4.58          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 4.40/4.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 4.40/4.58          | (v2_funct_1 @ X51)
% 4.40/4.58          | ((X49) = (k1_xboole_0))
% 4.40/4.58          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 4.40/4.58          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 4.40/4.58          | ~ (v1_funct_1 @ X51))),
% 4.40/4.58      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.40/4.58  thf('32', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i]:
% 4.40/4.58         (~ (v1_funct_1 @ X0)
% 4.40/4.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.40/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.40/4.58          | ((sk_A) = (k1_xboole_0))
% 4.40/4.58          | (v2_funct_1 @ X0)
% 4.40/4.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.40/4.58          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.40/4.58          | ~ (v1_funct_1 @ sk_D))),
% 4.40/4.58      inference('sup-', [status(thm)], ['30', '31'])).
% 4.40/4.58  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('35', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i]:
% 4.40/4.58         (~ (v1_funct_1 @ X0)
% 4.40/4.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.40/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.40/4.58          | ((sk_A) = (k1_xboole_0))
% 4.40/4.58          | (v2_funct_1 @ X0)
% 4.40/4.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.40/4.58      inference('demod', [status(thm)], ['32', '33', '34'])).
% 4.40/4.58  thf('36', plain,
% 4.40/4.58      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 4.40/4.58        | (v2_funct_1 @ sk_C)
% 4.40/4.58        | ((sk_A) = (k1_xboole_0))
% 4.40/4.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.40/4.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.40/4.58        | ~ (v1_funct_1 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['29', '35'])).
% 4.40/4.58  thf('37', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 4.40/4.58      inference('demod', [status(thm)], ['6', '7'])).
% 4.40/4.58  thf('38', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('41', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.40/4.58      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 4.40/4.58  thf('42', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.40/4.58      inference('split', [status(esa)], ['0'])).
% 4.40/4.58  thf('43', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.40/4.58      inference('sup-', [status(thm)], ['41', '42'])).
% 4.40/4.58  thf(fc4_zfmisc_1, axiom,
% 4.40/4.58    (![A:$i,B:$i]:
% 4.40/4.58     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.40/4.58  thf('44', plain,
% 4.40/4.58      (![X8 : $i, X9 : $i]:
% 4.40/4.58         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 4.40/4.58      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.40/4.58  thf('45', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf(cc1_subset_1, axiom,
% 4.40/4.58    (![A:$i]:
% 4.40/4.58     ( ( v1_xboole_0 @ A ) =>
% 4.40/4.58       ( ![B:$i]:
% 4.40/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.40/4.58  thf('46', plain,
% 4.40/4.58      (![X10 : $i, X11 : $i]:
% 4.40/4.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 4.40/4.58          | (v1_xboole_0 @ X10)
% 4.40/4.58          | ~ (v1_xboole_0 @ X11))),
% 4.40/4.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.40/4.58  thf('47', plain,
% 4.40/4.58      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['45', '46'])).
% 4.40/4.58  thf('48', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['44', '47'])).
% 4.40/4.58  thf('49', plain,
% 4.40/4.58      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 4.40/4.58         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.40/4.58      inference('sup-', [status(thm)], ['43', '48'])).
% 4.40/4.58  thf(d10_xboole_0, axiom,
% 4.40/4.58    (![A:$i,B:$i]:
% 4.40/4.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.40/4.58  thf('50', plain,
% 4.40/4.58      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 4.40/4.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.40/4.58  thf('51', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.40/4.58      inference('simplify', [status(thm)], ['50'])).
% 4.40/4.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 4.40/4.58  thf('52', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 4.40/4.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 4.40/4.58  thf(t69_xboole_1, axiom,
% 4.40/4.58    (![A:$i,B:$i]:
% 4.40/4.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 4.40/4.58       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 4.40/4.58  thf('53', plain,
% 4.40/4.58      (![X6 : $i, X7 : $i]:
% 4.40/4.58         (~ (r1_xboole_0 @ X6 @ X7)
% 4.40/4.58          | ~ (r1_tarski @ X6 @ X7)
% 4.40/4.58          | (v1_xboole_0 @ X6))),
% 4.40/4.58      inference('cnf', [status(esa)], [t69_xboole_1])).
% 4.40/4.58  thf('54', plain,
% 4.40/4.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.40/4.58      inference('sup-', [status(thm)], ['52', '53'])).
% 4.40/4.58  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.40/4.58      inference('sup-', [status(thm)], ['51', '54'])).
% 4.40/4.58  thf('56', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.40/4.58      inference('demod', [status(thm)], ['49', '55'])).
% 4.40/4.58  thf('57', plain, (((v2_funct_1 @ sk_C))),
% 4.40/4.58      inference('demod', [status(thm)], ['12', '56'])).
% 4.40/4.58  thf('58', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 4.40/4.58      inference('split', [status(esa)], ['0'])).
% 4.40/4.58  thf('59', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.40/4.58      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 4.40/4.58  thf('60', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 4.40/4.58      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 4.40/4.58  thf('61', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('62', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf(redefinition_k1_partfun1, axiom,
% 4.40/4.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.40/4.58     ( ( ( v1_funct_1 @ E ) & 
% 4.40/4.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.40/4.58         ( v1_funct_1 @ F ) & 
% 4.40/4.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.40/4.58       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.40/4.58  thf('63', plain,
% 4.40/4.58      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 4.40/4.58         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 4.40/4.58          | ~ (v1_funct_1 @ X40)
% 4.40/4.58          | ~ (v1_funct_1 @ X43)
% 4.40/4.58          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 4.40/4.58          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 4.40/4.58              = (k5_relat_1 @ X40 @ X43)))),
% 4.40/4.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.40/4.58  thf('64', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.40/4.58         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.40/4.58            = (k5_relat_1 @ sk_C @ X0))
% 4.40/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.40/4.58          | ~ (v1_funct_1 @ X0)
% 4.40/4.58          | ~ (v1_funct_1 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['62', '63'])).
% 4.40/4.58  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('66', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.40/4.58         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.40/4.58            = (k5_relat_1 @ sk_C @ X0))
% 4.40/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.40/4.58          | ~ (v1_funct_1 @ X0))),
% 4.40/4.58      inference('demod', [status(thm)], ['64', '65'])).
% 4.40/4.58  thf('67', plain,
% 4.40/4.58      ((~ (v1_funct_1 @ sk_D)
% 4.40/4.58        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.40/4.58            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.40/4.58      inference('sup-', [status(thm)], ['61', '66'])).
% 4.40/4.58  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('69', plain,
% 4.40/4.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.40/4.58         = (k6_partfun1 @ sk_A))),
% 4.40/4.58      inference('demod', [status(thm)], ['25', '28'])).
% 4.40/4.58  thf('70', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 4.40/4.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 4.40/4.58  thf(t45_relat_1, axiom,
% 4.40/4.58    (![A:$i]:
% 4.40/4.58     ( ( v1_relat_1 @ A ) =>
% 4.40/4.58       ( ![B:$i]:
% 4.40/4.58         ( ( v1_relat_1 @ B ) =>
% 4.40/4.58           ( r1_tarski @
% 4.40/4.58             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.40/4.58  thf('71', plain,
% 4.40/4.58      (![X18 : $i, X19 : $i]:
% 4.40/4.58         (~ (v1_relat_1 @ X18)
% 4.40/4.58          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 4.40/4.58             (k2_relat_1 @ X18))
% 4.40/4.58          | ~ (v1_relat_1 @ X19))),
% 4.40/4.58      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.40/4.58  thf('72', plain,
% 4.40/4.58      (![X1 : $i, X3 : $i]:
% 4.40/4.58         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 4.40/4.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.40/4.58  thf('73', plain,
% 4.40/4.58      (![X0 : $i, X1 : $i]:
% 4.40/4.58         (~ (v1_relat_1 @ X1)
% 4.40/4.58          | ~ (v1_relat_1 @ X0)
% 4.40/4.58          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 4.40/4.58               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 4.40/4.58          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 4.40/4.58      inference('sup-', [status(thm)], ['71', '72'])).
% 4.40/4.58  thf('74', plain,
% 4.40/4.58      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.40/4.58           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 4.40/4.58        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.40/4.58        | ~ (v1_relat_1 @ sk_D)
% 4.40/4.58        | ~ (v1_relat_1 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['70', '73'])).
% 4.40/4.58  thf(t71_relat_1, axiom,
% 4.40/4.58    (![A:$i]:
% 4.40/4.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.40/4.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.40/4.58  thf('75', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 4.40/4.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.40/4.58  thf('76', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.40/4.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.40/4.58  thf('77', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 4.40/4.58      inference('demod', [status(thm)], ['75', '76'])).
% 4.40/4.58  thf('78', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf(cc2_relset_1, axiom,
% 4.40/4.58    (![A:$i,B:$i,C:$i]:
% 4.40/4.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.40/4.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.40/4.58  thf('79', plain,
% 4.40/4.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.40/4.58         ((v5_relat_1 @ X24 @ X26)
% 4.40/4.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.40/4.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.40/4.58  thf('80', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.40/4.58      inference('sup-', [status(thm)], ['78', '79'])).
% 4.40/4.58  thf(d19_relat_1, axiom,
% 4.40/4.58    (![A:$i,B:$i]:
% 4.40/4.58     ( ( v1_relat_1 @ B ) =>
% 4.40/4.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.40/4.58  thf('81', plain,
% 4.40/4.58      (![X14 : $i, X15 : $i]:
% 4.40/4.58         (~ (v5_relat_1 @ X14 @ X15)
% 4.40/4.58          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.40/4.58          | ~ (v1_relat_1 @ X14))),
% 4.40/4.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.40/4.58  thf('82', plain,
% 4.40/4.58      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.40/4.58      inference('sup-', [status(thm)], ['80', '81'])).
% 4.40/4.58  thf('83', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf(cc2_relat_1, axiom,
% 4.40/4.58    (![A:$i]:
% 4.40/4.58     ( ( v1_relat_1 @ A ) =>
% 4.40/4.58       ( ![B:$i]:
% 4.40/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.40/4.58  thf('84', plain,
% 4.40/4.58      (![X12 : $i, X13 : $i]:
% 4.40/4.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.40/4.58          | (v1_relat_1 @ X12)
% 4.40/4.58          | ~ (v1_relat_1 @ X13))),
% 4.40/4.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.40/4.58  thf('85', plain,
% 4.40/4.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.40/4.58      inference('sup-', [status(thm)], ['83', '84'])).
% 4.40/4.58  thf(fc6_relat_1, axiom,
% 4.40/4.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.40/4.58  thf('86', plain,
% 4.40/4.58      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.40/4.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.40/4.58  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 4.40/4.58      inference('demod', [status(thm)], ['85', '86'])).
% 4.40/4.58  thf('88', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.40/4.58      inference('demod', [status(thm)], ['82', '87'])).
% 4.40/4.58  thf('89', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 4.40/4.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 4.40/4.58  thf('90', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 4.40/4.58      inference('demod', [status(thm)], ['75', '76'])).
% 4.40/4.58  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 4.40/4.58      inference('demod', [status(thm)], ['85', '86'])).
% 4.40/4.58  thf('92', plain,
% 4.40/4.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.40/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.40/4.58  thf('93', plain,
% 4.40/4.58      (![X12 : $i, X13 : $i]:
% 4.40/4.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.40/4.58          | (v1_relat_1 @ X12)
% 4.40/4.58          | ~ (v1_relat_1 @ X13))),
% 4.40/4.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.40/4.58  thf('94', plain,
% 4.40/4.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.40/4.58      inference('sup-', [status(thm)], ['92', '93'])).
% 4.40/4.58  thf('95', plain,
% 4.40/4.58      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.40/4.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.40/4.58  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 4.40/4.58      inference('demod', [status(thm)], ['94', '95'])).
% 4.40/4.58  thf('97', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.40/4.58      inference('demod', [status(thm)],
% 4.40/4.58                ['74', '77', '88', '89', '90', '91', '96'])).
% 4.40/4.58  thf('98', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.40/4.58      inference('simplify', [status(thm)], ['50'])).
% 4.40/4.58  thf('99', plain,
% 4.40/4.58      (![X14 : $i, X15 : $i]:
% 4.40/4.58         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.40/4.58          | (v5_relat_1 @ X14 @ X15)
% 4.40/4.58          | ~ (v1_relat_1 @ X14))),
% 4.40/4.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.40/4.58  thf('100', plain,
% 4.40/4.58      (![X0 : $i]:
% 4.40/4.58         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.40/4.58      inference('sup-', [status(thm)], ['98', '99'])).
% 4.40/4.58  thf(d3_funct_2, axiom,
% 4.40/4.58    (![A:$i,B:$i]:
% 4.40/4.58     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.40/4.58       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.40/4.58  thf('101', plain,
% 4.40/4.58      (![X32 : $i, X33 : $i]:
% 4.40/4.58         (((k2_relat_1 @ X33) != (X32))
% 4.40/4.58          | (v2_funct_2 @ X33 @ X32)
% 4.40/4.58          | ~ (v5_relat_1 @ X33 @ X32)
% 4.40/4.58          | ~ (v1_relat_1 @ X33))),
% 4.40/4.58      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.40/4.58  thf('102', plain,
% 4.40/4.58      (![X33 : $i]:
% 4.40/4.58         (~ (v1_relat_1 @ X33)
% 4.40/4.58          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 4.40/4.58          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 4.40/4.58      inference('simplify', [status(thm)], ['101'])).
% 4.40/4.58  thf('103', plain,
% 4.40/4.58      (![X0 : $i]:
% 4.40/4.58         (~ (v1_relat_1 @ X0)
% 4.40/4.58          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.40/4.58          | ~ (v1_relat_1 @ X0))),
% 4.40/4.58      inference('sup-', [status(thm)], ['100', '102'])).
% 4.40/4.58  thf('104', plain,
% 4.40/4.58      (![X0 : $i]:
% 4.40/4.58         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.40/4.58      inference('simplify', [status(thm)], ['103'])).
% 4.40/4.58  thf('105', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.40/4.58      inference('sup+', [status(thm)], ['97', '104'])).
% 4.40/4.58  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 4.40/4.58      inference('demod', [status(thm)], ['85', '86'])).
% 4.40/4.58  thf('107', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.40/4.58      inference('demod', [status(thm)], ['105', '106'])).
% 4.40/4.58  thf('108', plain, ($false), inference('demod', [status(thm)], ['60', '107'])).
% 4.40/4.58  
% 4.40/4.58  % SZS output end Refutation
% 4.40/4.58  
% 4.40/4.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
