%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UMEEkRRIt3

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:05 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 288 expanded)
%              Number of leaves         :   39 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          : 1112 (5447 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
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
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
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
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('27',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35 ) )
      | ( v2_funct_1 @ X39 )
      | ( X37 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
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

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','49','50'])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['12','51'])).

thf('53',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['63','67','70','71','72','73'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('76',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['63','67','70','71','72','73'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['77','80','81','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['55','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UMEEkRRIt3
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.31/3.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.31/3.50  % Solved by: fo/fo7.sh
% 3.31/3.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.31/3.50  % done 3877 iterations in 3.057s
% 3.31/3.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.31/3.50  % SZS output start Refutation
% 3.31/3.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.31/3.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.31/3.50  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.31/3.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.31/3.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.31/3.50  thf(sk_D_type, type, sk_D: $i).
% 3.31/3.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.31/3.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.31/3.50  thf(sk_A_type, type, sk_A: $i).
% 3.31/3.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.31/3.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.31/3.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.31/3.50  thf(sk_B_type, type, sk_B: $i).
% 3.31/3.50  thf(sk_C_type, type, sk_C: $i).
% 3.31/3.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.31/3.50  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.31/3.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.31/3.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.31/3.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.31/3.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.31/3.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.31/3.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.31/3.50  thf(t29_funct_2, conjecture,
% 3.31/3.50    (![A:$i,B:$i,C:$i]:
% 3.31/3.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.31/3.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.50       ( ![D:$i]:
% 3.31/3.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.31/3.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.31/3.50           ( ( r2_relset_1 @
% 3.31/3.50               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.31/3.50               ( k6_partfun1 @ A ) ) =>
% 3.31/3.50             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.31/3.50  thf(zf_stmt_0, negated_conjecture,
% 3.31/3.50    (~( ![A:$i,B:$i,C:$i]:
% 3.31/3.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.31/3.50            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.50          ( ![D:$i]:
% 3.31/3.50            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.31/3.50                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.31/3.50              ( ( r2_relset_1 @
% 3.31/3.50                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.31/3.50                  ( k6_partfun1 @ A ) ) =>
% 3.31/3.50                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.31/3.50    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.31/3.50  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('1', plain,
% 3.31/3.50      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.31/3.50      inference('split', [status(esa)], ['0'])).
% 3.31/3.50  thf(l13_xboole_0, axiom,
% 3.31/3.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.31/3.50  thf('2', plain,
% 3.31/3.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.31/3.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.31/3.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.31/3.50  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.31/3.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.31/3.50  thf(redefinition_k6_partfun1, axiom,
% 3.31/3.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.31/3.50  thf('4', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 3.31/3.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.31/3.50  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.31/3.50      inference('demod', [status(thm)], ['3', '4'])).
% 3.31/3.50  thf(fc4_funct_1, axiom,
% 3.31/3.50    (![A:$i]:
% 3.31/3.50     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.31/3.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.31/3.50  thf('6', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 3.31/3.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.31/3.50  thf('7', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 3.31/3.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.31/3.50  thf('8', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 3.31/3.50      inference('demod', [status(thm)], ['6', '7'])).
% 3.31/3.50  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.31/3.50      inference('sup+', [status(thm)], ['5', '8'])).
% 3.31/3.50  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.31/3.50      inference('sup+', [status(thm)], ['2', '9'])).
% 3.31/3.50  thf('11', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.31/3.50      inference('split', [status(esa)], ['0'])).
% 3.31/3.50  thf('12', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.31/3.50      inference('sup-', [status(thm)], ['10', '11'])).
% 3.31/3.50  thf('13', plain,
% 3.31/3.50      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.31/3.50        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.31/3.50        (k6_partfun1 @ sk_A))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('14', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('15', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(dt_k1_partfun1, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.31/3.50     ( ( ( v1_funct_1 @ E ) & 
% 3.31/3.50         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.31/3.50         ( v1_funct_1 @ F ) & 
% 3.31/3.50         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.31/3.50       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.31/3.50         ( m1_subset_1 @
% 3.31/3.50           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.31/3.50           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.31/3.50  thf('16', plain,
% 3.31/3.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.31/3.50         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.31/3.50          | ~ (v1_funct_1 @ X24)
% 3.31/3.50          | ~ (v1_funct_1 @ X27)
% 3.31/3.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.31/3.50          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 3.31/3.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 3.31/3.50      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.31/3.50  thf('17', plain,
% 3.31/3.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.31/3.50         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.31/3.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.31/3.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.31/3.50          | ~ (v1_funct_1 @ X1)
% 3.31/3.50          | ~ (v1_funct_1 @ sk_C))),
% 3.31/3.50      inference('sup-', [status(thm)], ['15', '16'])).
% 3.31/3.50  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('19', plain,
% 3.31/3.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.31/3.50         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.31/3.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.31/3.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.31/3.50          | ~ (v1_funct_1 @ X1))),
% 3.31/3.50      inference('demod', [status(thm)], ['17', '18'])).
% 3.31/3.50  thf('20', plain,
% 3.31/3.50      ((~ (v1_funct_1 @ sk_D)
% 3.31/3.50        | (m1_subset_1 @ 
% 3.31/3.50           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.31/3.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.31/3.50      inference('sup-', [status(thm)], ['14', '19'])).
% 3.31/3.50  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('22', plain,
% 3.31/3.50      ((m1_subset_1 @ 
% 3.31/3.50        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.31/3.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.31/3.50      inference('demod', [status(thm)], ['20', '21'])).
% 3.31/3.50  thf(redefinition_r2_relset_1, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i,D:$i]:
% 3.31/3.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.31/3.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.50       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.31/3.50  thf('23', plain,
% 3.31/3.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.31/3.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.31/3.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.31/3.50          | ((X17) = (X20))
% 3.31/3.50          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 3.31/3.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.31/3.50  thf('24', plain,
% 3.31/3.50      (![X0 : $i]:
% 3.31/3.50         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.31/3.50             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.31/3.50          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.31/3.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.31/3.50      inference('sup-', [status(thm)], ['22', '23'])).
% 3.31/3.50  thf('25', plain,
% 3.31/3.50      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.31/3.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.31/3.50        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.31/3.50            = (k6_partfun1 @ sk_A)))),
% 3.31/3.50      inference('sup-', [status(thm)], ['13', '24'])).
% 3.31/3.50  thf(t29_relset_1, axiom,
% 3.31/3.50    (![A:$i]:
% 3.31/3.50     ( m1_subset_1 @
% 3.31/3.50       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.31/3.50  thf('26', plain,
% 3.31/3.50      (![X21 : $i]:
% 3.31/3.50         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 3.31/3.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.31/3.50      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.31/3.50  thf('27', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 3.31/3.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.31/3.50  thf('28', plain,
% 3.31/3.50      (![X21 : $i]:
% 3.31/3.50         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.31/3.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.31/3.50      inference('demod', [status(thm)], ['26', '27'])).
% 3.31/3.50  thf('29', plain,
% 3.31/3.50      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.31/3.50         = (k6_partfun1 @ sk_A))),
% 3.31/3.50      inference('demod', [status(thm)], ['25', '28'])).
% 3.31/3.50  thf('30', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(t26_funct_2, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i,D:$i]:
% 3.31/3.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.31/3.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.50       ( ![E:$i]:
% 3.31/3.50         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.31/3.50             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.31/3.50           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.31/3.50             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.31/3.50               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.31/3.50  thf('31', plain,
% 3.31/3.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.31/3.50         (~ (v1_funct_1 @ X35)
% 3.31/3.50          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.31/3.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.31/3.50          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 3.31/3.50          | (v2_funct_1 @ X39)
% 3.31/3.50          | ((X37) = (k1_xboole_0))
% 3.31/3.50          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 3.31/3.50          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 3.31/3.50          | ~ (v1_funct_1 @ X39))),
% 3.31/3.50      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.31/3.50  thf('32', plain,
% 3.31/3.50      (![X0 : $i, X1 : $i]:
% 3.31/3.50         (~ (v1_funct_1 @ X0)
% 3.31/3.50          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.31/3.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.31/3.50          | ((sk_A) = (k1_xboole_0))
% 3.31/3.50          | (v2_funct_1 @ X0)
% 3.31/3.50          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.31/3.50          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.31/3.50          | ~ (v1_funct_1 @ sk_D))),
% 3.31/3.50      inference('sup-', [status(thm)], ['30', '31'])).
% 3.31/3.50  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('35', plain,
% 3.31/3.50      (![X0 : $i, X1 : $i]:
% 3.31/3.50         (~ (v1_funct_1 @ X0)
% 3.31/3.50          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.31/3.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.31/3.50          | ((sk_A) = (k1_xboole_0))
% 3.31/3.50          | (v2_funct_1 @ X0)
% 3.31/3.50          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.31/3.50      inference('demod', [status(thm)], ['32', '33', '34'])).
% 3.31/3.50  thf('36', plain,
% 3.31/3.50      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.31/3.50        | (v2_funct_1 @ sk_C)
% 3.31/3.50        | ((sk_A) = (k1_xboole_0))
% 3.31/3.50        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.31/3.50        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.31/3.50        | ~ (v1_funct_1 @ sk_C))),
% 3.31/3.50      inference('sup-', [status(thm)], ['29', '35'])).
% 3.31/3.50  thf('37', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 3.31/3.50      inference('demod', [status(thm)], ['6', '7'])).
% 3.31/3.50  thf('38', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('41', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.31/3.50      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 3.31/3.50  thf('42', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.31/3.50      inference('split', [status(esa)], ['0'])).
% 3.31/3.50  thf('43', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.31/3.50      inference('sup-', [status(thm)], ['41', '42'])).
% 3.31/3.50  thf('44', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(cc1_subset_1, axiom,
% 3.31/3.50    (![A:$i]:
% 3.31/3.50     ( ( v1_xboole_0 @ A ) =>
% 3.31/3.50       ( ![B:$i]:
% 3.31/3.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.31/3.50  thf('45', plain,
% 3.31/3.50      (![X4 : $i, X5 : $i]:
% 3.31/3.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.31/3.50          | (v1_xboole_0 @ X4)
% 3.31/3.50          | ~ (v1_xboole_0 @ X5))),
% 3.31/3.50      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.31/3.50  thf('46', plain,
% 3.31/3.50      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.31/3.50      inference('sup-', [status(thm)], ['44', '45'])).
% 3.31/3.50  thf('47', plain,
% 3.31/3.50      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 3.31/3.50         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.31/3.50      inference('sup-', [status(thm)], ['43', '46'])).
% 3.31/3.50  thf(t113_zfmisc_1, axiom,
% 3.31/3.50    (![A:$i,B:$i]:
% 3.31/3.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.31/3.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.31/3.50  thf('48', plain,
% 3.31/3.50      (![X2 : $i, X3 : $i]:
% 3.31/3.50         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 3.31/3.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.31/3.50  thf('49', plain,
% 3.31/3.50      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 3.31/3.50      inference('simplify', [status(thm)], ['48'])).
% 3.31/3.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.31/3.50  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.31/3.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.31/3.50  thf('51', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.31/3.50      inference('demod', [status(thm)], ['47', '49', '50'])).
% 3.31/3.50  thf('52', plain, (((v2_funct_1 @ sk_C))),
% 3.31/3.50      inference('demod', [status(thm)], ['12', '51'])).
% 3.31/3.50  thf('53', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.31/3.50      inference('split', [status(esa)], ['0'])).
% 3.31/3.50  thf('54', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.31/3.50      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 3.31/3.50  thf('55', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.31/3.50      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 3.31/3.50  thf('56', plain,
% 3.31/3.50      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.31/3.50         = (k6_partfun1 @ sk_A))),
% 3.31/3.50      inference('demod', [status(thm)], ['25', '28'])).
% 3.31/3.50  thf('57', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(t24_funct_2, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i]:
% 3.31/3.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.31/3.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.31/3.50       ( ![D:$i]:
% 3.31/3.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.31/3.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.31/3.50           ( ( r2_relset_1 @
% 3.31/3.50               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.31/3.50               ( k6_partfun1 @ B ) ) =>
% 3.31/3.50             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.31/3.50  thf('58', plain,
% 3.31/3.50      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.31/3.50         (~ (v1_funct_1 @ X31)
% 3.31/3.50          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 3.31/3.50          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.31/3.50          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 3.31/3.50               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 3.31/3.50               (k6_partfun1 @ X32))
% 3.31/3.50          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 3.31/3.50          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.31/3.50          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 3.31/3.50          | ~ (v1_funct_1 @ X34))),
% 3.31/3.50      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.31/3.50  thf('59', plain,
% 3.31/3.50      (![X0 : $i]:
% 3.31/3.50         (~ (v1_funct_1 @ X0)
% 3.31/3.50          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.31/3.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.31/3.50          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.31/3.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.31/3.50               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.31/3.50               (k6_partfun1 @ sk_A))
% 3.31/3.50          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.31/3.50          | ~ (v1_funct_1 @ sk_C))),
% 3.31/3.50      inference('sup-', [status(thm)], ['57', '58'])).
% 3.31/3.50  thf('60', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('62', plain,
% 3.31/3.50      (![X0 : $i]:
% 3.31/3.50         (~ (v1_funct_1 @ X0)
% 3.31/3.50          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.31/3.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.31/3.50          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.31/3.50          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.31/3.50               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.31/3.50               (k6_partfun1 @ sk_A)))),
% 3.31/3.50      inference('demod', [status(thm)], ['59', '60', '61'])).
% 3.31/3.50  thf('63', plain,
% 3.31/3.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 3.31/3.50           (k6_partfun1 @ sk_A))
% 3.31/3.50        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.31/3.50        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.31/3.50        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.31/3.50        | ~ (v1_funct_1 @ sk_D))),
% 3.31/3.50      inference('sup-', [status(thm)], ['56', '62'])).
% 3.31/3.50  thf('64', plain,
% 3.31/3.50      (![X21 : $i]:
% 3.31/3.50         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.31/3.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.31/3.50      inference('demod', [status(thm)], ['26', '27'])).
% 3.31/3.50  thf('65', plain,
% 3.31/3.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.31/3.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.31/3.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.31/3.50          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 3.31/3.50          | ((X17) != (X20)))),
% 3.31/3.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.31/3.50  thf('66', plain,
% 3.31/3.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.31/3.50         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 3.31/3.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.31/3.50      inference('simplify', [status(thm)], ['65'])).
% 3.31/3.50  thf('67', plain,
% 3.31/3.50      (![X0 : $i]:
% 3.31/3.50         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 3.31/3.50      inference('sup-', [status(thm)], ['64', '66'])).
% 3.31/3.50  thf('68', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(redefinition_k2_relset_1, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i]:
% 3.31/3.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.31/3.50  thf('69', plain,
% 3.31/3.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.31/3.50         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.31/3.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.31/3.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.31/3.50  thf('70', plain,
% 3.31/3.50      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.31/3.50      inference('sup-', [status(thm)], ['68', '69'])).
% 3.31/3.50  thf('71', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf('74', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.31/3.50      inference('demod', [status(thm)], ['63', '67', '70', '71', '72', '73'])).
% 3.31/3.50  thf(d3_funct_2, axiom,
% 3.31/3.50    (![A:$i,B:$i]:
% 3.31/3.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.31/3.50       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.31/3.50  thf('75', plain,
% 3.31/3.50      (![X22 : $i, X23 : $i]:
% 3.31/3.50         (((k2_relat_1 @ X23) != (X22))
% 3.31/3.50          | (v2_funct_2 @ X23 @ X22)
% 3.31/3.50          | ~ (v5_relat_1 @ X23 @ X22)
% 3.31/3.50          | ~ (v1_relat_1 @ X23))),
% 3.31/3.50      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.31/3.50  thf('76', plain,
% 3.31/3.50      (![X23 : $i]:
% 3.31/3.50         (~ (v1_relat_1 @ X23)
% 3.31/3.50          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 3.31/3.50          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 3.31/3.50      inference('simplify', [status(thm)], ['75'])).
% 3.31/3.50  thf('77', plain,
% 3.31/3.50      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.31/3.50        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.31/3.50        | ~ (v1_relat_1 @ sk_D))),
% 3.31/3.50      inference('sup-', [status(thm)], ['74', '76'])).
% 3.31/3.50  thf('78', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(cc2_relset_1, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i]:
% 3.31/3.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.31/3.50  thf('79', plain,
% 3.31/3.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.31/3.50         ((v5_relat_1 @ X11 @ X13)
% 3.31/3.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.31/3.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.31/3.50  thf('80', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.31/3.50      inference('sup-', [status(thm)], ['78', '79'])).
% 3.31/3.50  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.31/3.50      inference('demod', [status(thm)], ['63', '67', '70', '71', '72', '73'])).
% 3.31/3.50  thf('82', plain,
% 3.31/3.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.31/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.50  thf(cc1_relset_1, axiom,
% 3.31/3.50    (![A:$i,B:$i,C:$i]:
% 3.31/3.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.31/3.50       ( v1_relat_1 @ C ) ))).
% 3.31/3.50  thf('83', plain,
% 3.31/3.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.31/3.50         ((v1_relat_1 @ X8)
% 3.31/3.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.31/3.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.31/3.50  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 3.31/3.50      inference('sup-', [status(thm)], ['82', '83'])).
% 3.31/3.50  thf('85', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.31/3.50      inference('demod', [status(thm)], ['77', '80', '81', '84'])).
% 3.31/3.50  thf('86', plain, ($false), inference('demod', [status(thm)], ['55', '85'])).
% 3.31/3.50  
% 3.31/3.50  % SZS output end Refutation
% 3.31/3.50  
% 3.34/3.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
