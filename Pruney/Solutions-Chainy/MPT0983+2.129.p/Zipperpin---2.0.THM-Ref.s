%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w2wD0CHz0F

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:21 EST 2020

% Result     : Theorem 3.24s
% Output     : Refutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 305 expanded)
%              Number of leaves         :   41 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          : 1209 (5652 expanded)
%              Number of equality atoms :   44 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('10',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(clc,[status(thm)],['4','11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('29',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('30',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('34',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45 ) )
      | ( v2_funct_1 @ X49 )
      | ( X47 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','52','53'])).

thf('55',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['13','54'])).

thf('56',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('61',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('62',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_relat_1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('74',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['68','72','75','76','77','78'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('80',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ X31 )
       != X30 )
      | ( v2_funct_2 @ X31 @ X30 )
      | ~ ( v5_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('81',plain,(
    ! [X31: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v5_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
      | ( v2_funct_2 @ X31 @ ( k2_relat_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['68','72','75','76','77','78'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['82','85','86','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['58','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w2wD0CHz0F
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.24/3.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.24/3.47  % Solved by: fo/fo7.sh
% 3.24/3.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.24/3.47  % done 3613 iterations in 3.014s
% 3.24/3.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.24/3.47  % SZS output start Refutation
% 3.24/3.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.24/3.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.24/3.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.24/3.47  thf(sk_C_type, type, sk_C: $i).
% 3.24/3.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.24/3.47  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.24/3.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.24/3.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.24/3.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.24/3.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.24/3.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.24/3.47  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.24/3.47  thf(sk_D_type, type, sk_D: $i).
% 3.24/3.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.24/3.47  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.24/3.47  thf(sk_A_type, type, sk_A: $i).
% 3.24/3.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.24/3.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.24/3.47  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.24/3.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.24/3.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.24/3.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.24/3.47  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.24/3.47  thf(t29_funct_2, conjecture,
% 3.24/3.47    (![A:$i,B:$i,C:$i]:
% 3.24/3.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.24/3.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.24/3.47       ( ![D:$i]:
% 3.24/3.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.24/3.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.24/3.47           ( ( r2_relset_1 @
% 3.24/3.47               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.24/3.47               ( k6_partfun1 @ A ) ) =>
% 3.24/3.47             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.24/3.47  thf(zf_stmt_0, negated_conjecture,
% 3.24/3.47    (~( ![A:$i,B:$i,C:$i]:
% 3.24/3.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.24/3.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.24/3.47          ( ![D:$i]:
% 3.24/3.47            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.24/3.47                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.24/3.47              ( ( r2_relset_1 @
% 3.24/3.47                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.24/3.47                  ( k6_partfun1 @ A ) ) =>
% 3.24/3.47                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.24/3.47    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.24/3.47  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf('1', plain,
% 3.24/3.47      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.24/3.47      inference('split', [status(esa)], ['0'])).
% 3.24/3.47  thf(t8_boole, axiom,
% 3.24/3.47    (![A:$i,B:$i]:
% 3.24/3.47     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.24/3.47  thf('2', plain,
% 3.24/3.47      (![X3 : $i, X4 : $i]:
% 3.24/3.47         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.24/3.47      inference('cnf', [status(esa)], [t8_boole])).
% 3.24/3.47  thf('3', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.47      inference('split', [status(esa)], ['0'])).
% 3.24/3.47  thf('4', plain,
% 3.24/3.47      ((![X0 : $i]:
% 3.24/3.47          (~ (v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_C)))
% 3.24/3.47         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.47      inference('sup-', [status(thm)], ['2', '3'])).
% 3.24/3.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.24/3.47  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.24/3.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.24/3.47  thf('6', plain,
% 3.24/3.47      (![X3 : $i, X4 : $i]:
% 3.24/3.47         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.24/3.47      inference('cnf', [status(esa)], [t8_boole])).
% 3.24/3.47  thf('7', plain,
% 3.24/3.47      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.24/3.47      inference('sup-', [status(thm)], ['5', '6'])).
% 3.24/3.47  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.24/3.47  thf('8', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.24/3.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.24/3.47  thf(fc4_funct_1, axiom,
% 3.24/3.47    (![A:$i]:
% 3.24/3.47     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.24/3.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.24/3.47  thf('9', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 3.24/3.47      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.24/3.47  thf('10', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.24/3.47      inference('sup+', [status(thm)], ['8', '9'])).
% 3.24/3.47  thf('11', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.24/3.47      inference('sup+', [status(thm)], ['7', '10'])).
% 3.24/3.47  thf('12', plain,
% 3.24/3.47      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 3.24/3.47         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.47      inference('clc', [status(thm)], ['4', '11'])).
% 3.24/3.47  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.47      inference('condensation', [status(thm)], ['12'])).
% 3.24/3.47  thf('14', plain,
% 3.24/3.47      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.24/3.47        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.24/3.47        (k6_partfun1 @ sk_A))),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf(redefinition_k6_partfun1, axiom,
% 3.24/3.47    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.24/3.47  thf('15', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 3.24/3.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.24/3.47  thf('16', plain,
% 3.24/3.47      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.24/3.47        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.24/3.47        (k6_relat_1 @ sk_A))),
% 3.24/3.47      inference('demod', [status(thm)], ['14', '15'])).
% 3.24/3.47  thf('17', plain,
% 3.24/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf('18', plain,
% 3.24/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf(dt_k1_partfun1, axiom,
% 3.24/3.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.24/3.47     ( ( ( v1_funct_1 @ E ) & 
% 3.24/3.47         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.24/3.47         ( v1_funct_1 @ F ) & 
% 3.24/3.47         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.24/3.47       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.24/3.47         ( m1_subset_1 @
% 3.24/3.47           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.24/3.47           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.24/3.47  thf('19', plain,
% 3.24/3.47      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.24/3.47         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.24/3.47          | ~ (v1_funct_1 @ X32)
% 3.24/3.47          | ~ (v1_funct_1 @ X35)
% 3.24/3.47          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.24/3.47          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 3.24/3.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 3.24/3.47      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.24/3.47  thf('20', plain,
% 3.24/3.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.47         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.24/3.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.24/3.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.24/3.47          | ~ (v1_funct_1 @ X1)
% 3.24/3.47          | ~ (v1_funct_1 @ sk_C))),
% 3.24/3.47      inference('sup-', [status(thm)], ['18', '19'])).
% 3.24/3.47  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf('22', plain,
% 3.24/3.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.47         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.24/3.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.24/3.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.24/3.47          | ~ (v1_funct_1 @ X1))),
% 3.24/3.47      inference('demod', [status(thm)], ['20', '21'])).
% 3.24/3.47  thf('23', plain,
% 3.24/3.47      ((~ (v1_funct_1 @ sk_D)
% 3.24/3.47        | (m1_subset_1 @ 
% 3.24/3.47           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.24/3.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.24/3.47      inference('sup-', [status(thm)], ['17', '22'])).
% 3.24/3.47  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf('25', plain,
% 3.24/3.47      ((m1_subset_1 @ 
% 3.24/3.47        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.24/3.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.24/3.47      inference('demod', [status(thm)], ['23', '24'])).
% 3.24/3.47  thf(redefinition_r2_relset_1, axiom,
% 3.24/3.47    (![A:$i,B:$i,C:$i,D:$i]:
% 3.24/3.47     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.24/3.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.24/3.47       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.24/3.47  thf('26', plain,
% 3.24/3.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.24/3.47         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.24/3.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.24/3.47          | ((X26) = (X29))
% 3.24/3.47          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 3.24/3.47      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.24/3.47  thf('27', plain,
% 3.24/3.47      (![X0 : $i]:
% 3.24/3.47         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.24/3.47             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 3.24/3.47          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 3.24/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.24/3.47      inference('sup-', [status(thm)], ['25', '26'])).
% 3.24/3.47  thf('28', plain,
% 3.24/3.47      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.24/3.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.24/3.47        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.24/3.47            = (k6_relat_1 @ sk_A)))),
% 3.24/3.47      inference('sup-', [status(thm)], ['16', '27'])).
% 3.24/3.47  thf(dt_k6_partfun1, axiom,
% 3.24/3.47    (![A:$i]:
% 3.24/3.47     ( ( m1_subset_1 @
% 3.24/3.47         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.24/3.47       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.24/3.47  thf('29', plain,
% 3.24/3.47      (![X39 : $i]:
% 3.24/3.47         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 3.24/3.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 3.24/3.47      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.24/3.47  thf('30', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 3.24/3.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.24/3.47  thf('31', plain,
% 3.24/3.47      (![X39 : $i]:
% 3.24/3.47         (m1_subset_1 @ (k6_relat_1 @ X39) @ 
% 3.24/3.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 3.24/3.47      inference('demod', [status(thm)], ['29', '30'])).
% 3.24/3.47  thf('32', plain,
% 3.24/3.47      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.24/3.47         = (k6_relat_1 @ sk_A))),
% 3.24/3.47      inference('demod', [status(thm)], ['28', '31'])).
% 3.24/3.47  thf('33', plain,
% 3.24/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf(t26_funct_2, axiom,
% 3.24/3.47    (![A:$i,B:$i,C:$i,D:$i]:
% 3.24/3.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.24/3.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.24/3.47       ( ![E:$i]:
% 3.24/3.47         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.24/3.47             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.24/3.47           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.24/3.47             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.24/3.47               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.24/3.47  thf('34', plain,
% 3.24/3.47      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 3.24/3.47         (~ (v1_funct_1 @ X45)
% 3.24/3.47          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 3.24/3.47          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 3.24/3.47          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45))
% 3.24/3.47          | (v2_funct_1 @ X49)
% 3.24/3.47          | ((X47) = (k1_xboole_0))
% 3.24/3.47          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 3.24/3.47          | ~ (v1_funct_2 @ X49 @ X48 @ X46)
% 3.24/3.47          | ~ (v1_funct_1 @ X49))),
% 3.24/3.47      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.24/3.47  thf('35', plain,
% 3.24/3.47      (![X0 : $i, X1 : $i]:
% 3.24/3.47         (~ (v1_funct_1 @ X0)
% 3.24/3.47          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.24/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.24/3.47          | ((sk_A) = (k1_xboole_0))
% 3.24/3.47          | (v2_funct_1 @ X0)
% 3.24/3.47          | ~ (v2_funct_1 @ 
% 3.24/3.47               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.24/3.47          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.24/3.47          | ~ (v1_funct_1 @ sk_D))),
% 3.24/3.47      inference('sup-', [status(thm)], ['33', '34'])).
% 3.24/3.47  thf('36', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 3.24/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.47  thf('38', plain,
% 3.24/3.48      (![X0 : $i, X1 : $i]:
% 3.24/3.48         (~ (v1_funct_1 @ X0)
% 3.24/3.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.24/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.24/3.48          | ((sk_A) = (k1_xboole_0))
% 3.24/3.48          | (v2_funct_1 @ X0)
% 3.24/3.48          | ~ (v2_funct_1 @ 
% 3.24/3.48               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.24/3.48      inference('demod', [status(thm)], ['35', '36', '37'])).
% 3.24/3.48  thf('39', plain,
% 3.24/3.48      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.24/3.48        | (v2_funct_1 @ sk_C)
% 3.24/3.48        | ((sk_A) = (k1_xboole_0))
% 3.24/3.48        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.24/3.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.24/3.48        | ~ (v1_funct_1 @ sk_C))),
% 3.24/3.48      inference('sup-', [status(thm)], ['32', '38'])).
% 3.24/3.48  thf('40', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 3.24/3.48      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.24/3.48  thf('41', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('44', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.24/3.48      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 3.24/3.48  thf('45', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.48      inference('split', [status(esa)], ['0'])).
% 3.24/3.48  thf('46', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.48      inference('sup-', [status(thm)], ['44', '45'])).
% 3.24/3.48  thf('47', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf(cc1_subset_1, axiom,
% 3.24/3.48    (![A:$i]:
% 3.24/3.48     ( ( v1_xboole_0 @ A ) =>
% 3.24/3.48       ( ![B:$i]:
% 3.24/3.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.24/3.48  thf('48', plain,
% 3.24/3.48      (![X9 : $i, X10 : $i]:
% 3.24/3.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.24/3.48          | (v1_xboole_0 @ X9)
% 3.24/3.48          | ~ (v1_xboole_0 @ X10))),
% 3.24/3.48      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.24/3.48  thf('49', plain,
% 3.24/3.48      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_xboole_0 @ sk_C))),
% 3.24/3.48      inference('sup-', [status(thm)], ['47', '48'])).
% 3.24/3.48  thf('50', plain,
% 3.24/3.48      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 3.24/3.48         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.48      inference('sup-', [status(thm)], ['46', '49'])).
% 3.24/3.48  thf(t113_zfmisc_1, axiom,
% 3.24/3.48    (![A:$i,B:$i]:
% 3.24/3.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.24/3.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.24/3.48  thf('51', plain,
% 3.24/3.48      (![X6 : $i, X7 : $i]:
% 3.24/3.48         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.24/3.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.24/3.48  thf('52', plain,
% 3.24/3.48      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.24/3.48      inference('simplify', [status(thm)], ['51'])).
% 3.24/3.48  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.24/3.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.24/3.48  thf('54', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.24/3.48      inference('demod', [status(thm)], ['50', '52', '53'])).
% 3.24/3.48  thf('55', plain, (((v2_funct_1 @ sk_C))),
% 3.24/3.48      inference('demod', [status(thm)], ['13', '54'])).
% 3.24/3.48  thf('56', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.24/3.48      inference('split', [status(esa)], ['0'])).
% 3.24/3.48  thf('57', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.24/3.48      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 3.24/3.48  thf('58', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.24/3.48      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 3.24/3.48  thf('59', plain,
% 3.24/3.48      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.24/3.48         = (k6_relat_1 @ sk_A))),
% 3.24/3.48      inference('demod', [status(thm)], ['28', '31'])).
% 3.24/3.48  thf('60', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf(t24_funct_2, axiom,
% 3.24/3.48    (![A:$i,B:$i,C:$i]:
% 3.24/3.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.24/3.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.24/3.48       ( ![D:$i]:
% 3.24/3.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.24/3.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.24/3.48           ( ( r2_relset_1 @
% 3.24/3.48               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.24/3.48               ( k6_partfun1 @ B ) ) =>
% 3.24/3.48             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.24/3.48  thf('61', plain,
% 3.24/3.48      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.24/3.48         (~ (v1_funct_1 @ X41)
% 3.24/3.48          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 3.24/3.48          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.24/3.48          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 3.24/3.48               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 3.24/3.48               (k6_partfun1 @ X42))
% 3.24/3.48          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 3.24/3.48          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 3.24/3.48          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 3.24/3.48          | ~ (v1_funct_1 @ X44))),
% 3.24/3.48      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.24/3.48  thf('62', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 3.24/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.24/3.48  thf('63', plain,
% 3.24/3.48      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.24/3.48         (~ (v1_funct_1 @ X41)
% 3.24/3.48          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 3.24/3.48          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.24/3.48          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 3.24/3.48               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 3.24/3.48               (k6_relat_1 @ X42))
% 3.24/3.48          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 3.24/3.48          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 3.24/3.48          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 3.24/3.48          | ~ (v1_funct_1 @ X44))),
% 3.24/3.48      inference('demod', [status(thm)], ['61', '62'])).
% 3.24/3.48  thf('64', plain,
% 3.24/3.48      (![X0 : $i]:
% 3.24/3.48         (~ (v1_funct_1 @ X0)
% 3.24/3.48          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.24/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.24/3.48          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.24/3.48          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.24/3.48               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.24/3.48               (k6_relat_1 @ sk_A))
% 3.24/3.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.24/3.48          | ~ (v1_funct_1 @ sk_C))),
% 3.24/3.48      inference('sup-', [status(thm)], ['60', '63'])).
% 3.24/3.48  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('67', plain,
% 3.24/3.48      (![X0 : $i]:
% 3.24/3.48         (~ (v1_funct_1 @ X0)
% 3.24/3.48          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.24/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.24/3.48          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.24/3.48          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.24/3.48               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.24/3.48               (k6_relat_1 @ sk_A)))),
% 3.24/3.48      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.24/3.48  thf('68', plain,
% 3.24/3.48      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.24/3.48           (k6_relat_1 @ sk_A))
% 3.24/3.48        | ((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 3.24/3.48        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.24/3.48        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.24/3.48        | ~ (v1_funct_1 @ sk_D))),
% 3.24/3.48      inference('sup-', [status(thm)], ['59', '67'])).
% 3.24/3.48  thf('69', plain,
% 3.24/3.48      (![X39 : $i]:
% 3.24/3.48         (m1_subset_1 @ (k6_relat_1 @ X39) @ 
% 3.24/3.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 3.24/3.48      inference('demod', [status(thm)], ['29', '30'])).
% 3.24/3.48  thf('70', plain,
% 3.24/3.48      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.24/3.48         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.24/3.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.24/3.48          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 3.24/3.48          | ((X26) != (X29)))),
% 3.24/3.48      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.24/3.48  thf('71', plain,
% 3.24/3.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.24/3.48         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 3.24/3.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.24/3.48      inference('simplify', [status(thm)], ['70'])).
% 3.24/3.48  thf('72', plain,
% 3.24/3.48      (![X0 : $i]:
% 3.24/3.48         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.24/3.48      inference('sup-', [status(thm)], ['69', '71'])).
% 3.24/3.48  thf('73', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf(redefinition_k2_relset_1, axiom,
% 3.24/3.48    (![A:$i,B:$i,C:$i]:
% 3.24/3.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.24/3.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.24/3.48  thf('74', plain,
% 3.24/3.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.24/3.48         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 3.24/3.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.24/3.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.24/3.48  thf('75', plain,
% 3.24/3.48      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.24/3.48      inference('sup-', [status(thm)], ['73', '74'])).
% 3.24/3.48  thf('76', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('77', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf('79', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.24/3.48      inference('demod', [status(thm)], ['68', '72', '75', '76', '77', '78'])).
% 3.24/3.48  thf(d3_funct_2, axiom,
% 3.24/3.48    (![A:$i,B:$i]:
% 3.24/3.48     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.24/3.48       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.24/3.48  thf('80', plain,
% 3.24/3.48      (![X30 : $i, X31 : $i]:
% 3.24/3.48         (((k2_relat_1 @ X31) != (X30))
% 3.24/3.48          | (v2_funct_2 @ X31 @ X30)
% 3.24/3.48          | ~ (v5_relat_1 @ X31 @ X30)
% 3.24/3.48          | ~ (v1_relat_1 @ X31))),
% 3.24/3.48      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.24/3.48  thf('81', plain,
% 3.24/3.48      (![X31 : $i]:
% 3.24/3.48         (~ (v1_relat_1 @ X31)
% 3.24/3.48          | ~ (v5_relat_1 @ X31 @ (k2_relat_1 @ X31))
% 3.24/3.48          | (v2_funct_2 @ X31 @ (k2_relat_1 @ X31)))),
% 3.24/3.48      inference('simplify', [status(thm)], ['80'])).
% 3.24/3.48  thf('82', plain,
% 3.24/3.48      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.24/3.48        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.24/3.48        | ~ (v1_relat_1 @ sk_D))),
% 3.24/3.48      inference('sup-', [status(thm)], ['79', '81'])).
% 3.24/3.48  thf('83', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf(cc2_relset_1, axiom,
% 3.24/3.48    (![A:$i,B:$i,C:$i]:
% 3.24/3.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.24/3.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.24/3.48  thf('84', plain,
% 3.24/3.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.24/3.48         ((v5_relat_1 @ X20 @ X22)
% 3.24/3.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.24/3.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.24/3.48  thf('85', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.24/3.48      inference('sup-', [status(thm)], ['83', '84'])).
% 3.24/3.48  thf('86', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.24/3.48      inference('demod', [status(thm)], ['68', '72', '75', '76', '77', '78'])).
% 3.24/3.48  thf('87', plain,
% 3.24/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.24/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.48  thf(cc2_relat_1, axiom,
% 3.24/3.48    (![A:$i]:
% 3.24/3.48     ( ( v1_relat_1 @ A ) =>
% 3.24/3.48       ( ![B:$i]:
% 3.24/3.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.24/3.48  thf('88', plain,
% 3.24/3.48      (![X14 : $i, X15 : $i]:
% 3.24/3.48         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.24/3.48          | (v1_relat_1 @ X14)
% 3.24/3.48          | ~ (v1_relat_1 @ X15))),
% 3.24/3.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.24/3.48  thf('89', plain,
% 3.24/3.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.24/3.48      inference('sup-', [status(thm)], ['87', '88'])).
% 3.24/3.48  thf(fc6_relat_1, axiom,
% 3.24/3.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.24/3.48  thf('90', plain,
% 3.24/3.48      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 3.24/3.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.24/3.48  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 3.24/3.48      inference('demod', [status(thm)], ['89', '90'])).
% 3.24/3.48  thf('92', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.24/3.48      inference('demod', [status(thm)], ['82', '85', '86', '91'])).
% 3.24/3.48  thf('93', plain, ($false), inference('demod', [status(thm)], ['58', '92'])).
% 3.24/3.48  
% 3.24/3.48  % SZS output end Refutation
% 3.24/3.48  
% 3.24/3.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
