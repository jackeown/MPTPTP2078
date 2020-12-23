%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dnSCcTxJaj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:22 EST 2020

% Result     : Theorem 4.12s
% Output     : Refutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 305 expanded)
%              Number of leaves         :   41 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          : 1206 (5646 expanded)
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

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
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
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('30',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
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
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_partfun1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('62',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_relat_1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
       != X29 )
      | ( v2_funct_2 @ X30 @ X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('81',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
      | ( v2_funct_2 @ X30 @ ( k2_relat_1 @ X30 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dnSCcTxJaj
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:44:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.12/4.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.12/4.32  % Solved by: fo/fo7.sh
% 4.12/4.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.12/4.32  % done 4523 iterations in 3.869s
% 4.12/4.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.12/4.32  % SZS output start Refutation
% 4.12/4.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.12/4.32  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.12/4.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.12/4.32  thf(sk_D_type, type, sk_D: $i).
% 4.12/4.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.12/4.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.12/4.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.12/4.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.12/4.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.12/4.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.12/4.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.12/4.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.12/4.32  thf(sk_C_type, type, sk_C: $i).
% 4.12/4.32  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.12/4.32  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.12/4.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.12/4.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.12/4.32  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.12/4.32  thf(sk_A_type, type, sk_A: $i).
% 4.12/4.32  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.12/4.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.12/4.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.12/4.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.12/4.32  thf(t29_funct_2, conjecture,
% 4.12/4.32    (![A:$i,B:$i,C:$i]:
% 4.12/4.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.12/4.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.32       ( ![D:$i]:
% 4.12/4.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.12/4.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.12/4.32           ( ( r2_relset_1 @
% 4.12/4.32               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.12/4.32               ( k6_partfun1 @ A ) ) =>
% 4.12/4.32             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.12/4.32  thf(zf_stmt_0, negated_conjecture,
% 4.12/4.32    (~( ![A:$i,B:$i,C:$i]:
% 4.12/4.32        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.12/4.32            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.32          ( ![D:$i]:
% 4.12/4.32            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.12/4.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.12/4.32              ( ( r2_relset_1 @
% 4.12/4.32                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.12/4.32                  ( k6_partfun1 @ A ) ) =>
% 4.12/4.32                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.12/4.32    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.12/4.32  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('1', plain,
% 4.12/4.32      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.12/4.32      inference('split', [status(esa)], ['0'])).
% 4.12/4.32  thf(t8_boole, axiom,
% 4.12/4.32    (![A:$i,B:$i]:
% 4.12/4.32     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.12/4.32  thf('2', plain,
% 4.12/4.32      (![X3 : $i, X4 : $i]:
% 4.12/4.32         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 4.12/4.32      inference('cnf', [status(esa)], [t8_boole])).
% 4.12/4.32  thf('3', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('split', [status(esa)], ['0'])).
% 4.12/4.32  thf('4', plain,
% 4.12/4.32      ((![X0 : $i]:
% 4.12/4.32          (~ (v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_C)))
% 4.12/4.32         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('sup-', [status(thm)], ['2', '3'])).
% 4.12/4.32  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.12/4.32  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.12/4.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.12/4.32  thf('6', plain,
% 4.12/4.32      (![X3 : $i, X4 : $i]:
% 4.12/4.32         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 4.12/4.32      inference('cnf', [status(esa)], [t8_boole])).
% 4.12/4.32  thf('7', plain,
% 4.12/4.32      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.12/4.32      inference('sup-', [status(thm)], ['5', '6'])).
% 4.12/4.32  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.12/4.32  thf('8', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.12/4.32      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.12/4.32  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 4.12/4.32  thf('9', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 4.12/4.32      inference('cnf', [status(esa)], [t52_funct_1])).
% 4.12/4.32  thf('10', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.12/4.32      inference('sup+', [status(thm)], ['8', '9'])).
% 4.12/4.32  thf('11', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.12/4.32      inference('sup+', [status(thm)], ['7', '10'])).
% 4.12/4.32  thf('12', plain,
% 4.12/4.32      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 4.12/4.32         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('clc', [status(thm)], ['4', '11'])).
% 4.12/4.32  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('condensation', [status(thm)], ['12'])).
% 4.12/4.32  thf('14', plain,
% 4.12/4.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.32        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 4.12/4.32        (k6_partfun1 @ sk_A))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(redefinition_k6_partfun1, axiom,
% 4.12/4.32    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.12/4.32  thf('15', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 4.12/4.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.12/4.32  thf('16', plain,
% 4.12/4.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.32        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 4.12/4.32        (k6_relat_1 @ sk_A))),
% 4.12/4.32      inference('demod', [status(thm)], ['14', '15'])).
% 4.12/4.32  thf('17', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('18', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(dt_k1_partfun1, axiom,
% 4.12/4.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.12/4.32     ( ( ( v1_funct_1 @ E ) & 
% 4.12/4.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.12/4.32         ( v1_funct_1 @ F ) & 
% 4.12/4.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.12/4.32       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.12/4.32         ( m1_subset_1 @
% 4.12/4.32           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.12/4.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.12/4.32  thf('19', plain,
% 4.12/4.32      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.12/4.32         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.12/4.32          | ~ (v1_funct_1 @ X31)
% 4.12/4.32          | ~ (v1_funct_1 @ X34)
% 4.12/4.32          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.12/4.32          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 4.12/4.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 4.12/4.32      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.12/4.32  thf('20', plain,
% 4.12/4.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.12/4.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 4.12/4.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.12/4.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.12/4.32          | ~ (v1_funct_1 @ X1)
% 4.12/4.32          | ~ (v1_funct_1 @ sk_C))),
% 4.12/4.32      inference('sup-', [status(thm)], ['18', '19'])).
% 4.12/4.32  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('22', plain,
% 4.12/4.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.12/4.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 4.12/4.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.12/4.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.12/4.32          | ~ (v1_funct_1 @ X1))),
% 4.12/4.32      inference('demod', [status(thm)], ['20', '21'])).
% 4.12/4.32  thf('23', plain,
% 4.12/4.32      ((~ (v1_funct_1 @ sk_D)
% 4.12/4.32        | (m1_subset_1 @ 
% 4.12/4.32           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 4.12/4.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.12/4.32      inference('sup-', [status(thm)], ['17', '22'])).
% 4.12/4.32  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('25', plain,
% 4.12/4.32      ((m1_subset_1 @ 
% 4.12/4.32        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 4.12/4.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.12/4.32      inference('demod', [status(thm)], ['23', '24'])).
% 4.12/4.32  thf(redefinition_r2_relset_1, axiom,
% 4.12/4.32    (![A:$i,B:$i,C:$i,D:$i]:
% 4.12/4.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.12/4.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.12/4.32  thf('26', plain,
% 4.12/4.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.12/4.32         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.12/4.32          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.12/4.32          | ((X25) = (X28))
% 4.12/4.32          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 4.12/4.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.12/4.32  thf('27', plain,
% 4.12/4.32      (![X0 : $i]:
% 4.12/4.32         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.32             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 4.12/4.32          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 4.12/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.12/4.32      inference('sup-', [status(thm)], ['25', '26'])).
% 4.12/4.32  thf('28', plain,
% 4.12/4.32      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 4.12/4.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.12/4.32        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 4.12/4.32            = (k6_relat_1 @ sk_A)))),
% 4.12/4.32      inference('sup-', [status(thm)], ['16', '27'])).
% 4.12/4.32  thf(dt_k6_partfun1, axiom,
% 4.12/4.32    (![A:$i]:
% 4.12/4.32     ( ( m1_subset_1 @
% 4.12/4.32         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.12/4.32       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.12/4.32  thf('29', plain,
% 4.12/4.32      (![X38 : $i]:
% 4.12/4.32         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 4.12/4.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 4.12/4.32      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.12/4.32  thf('30', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 4.12/4.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.12/4.32  thf('31', plain,
% 4.12/4.32      (![X38 : $i]:
% 4.12/4.32         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 4.12/4.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 4.12/4.32      inference('demod', [status(thm)], ['29', '30'])).
% 4.12/4.32  thf('32', plain,
% 4.12/4.32      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 4.12/4.32         = (k6_relat_1 @ sk_A))),
% 4.12/4.32      inference('demod', [status(thm)], ['28', '31'])).
% 4.12/4.32  thf('33', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(t26_funct_2, axiom,
% 4.12/4.32    (![A:$i,B:$i,C:$i,D:$i]:
% 4.12/4.32     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.12/4.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.32       ( ![E:$i]:
% 4.12/4.32         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.12/4.32             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.12/4.32           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.12/4.32             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.12/4.32               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.12/4.32  thf('34', plain,
% 4.12/4.32      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X44)
% 4.12/4.32          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 4.12/4.32          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 4.12/4.32          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 4.12/4.32          | (v2_funct_1 @ X48)
% 4.12/4.32          | ((X46) = (k1_xboole_0))
% 4.12/4.32          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 4.12/4.32          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 4.12/4.32          | ~ (v1_funct_1 @ X48))),
% 4.12/4.32      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.12/4.32  thf('35', plain,
% 4.12/4.32      (![X0 : $i, X1 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X0)
% 4.12/4.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 4.12/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 4.12/4.32          | ((sk_A) = (k1_xboole_0))
% 4.12/4.32          | (v2_funct_1 @ X0)
% 4.12/4.32          | ~ (v2_funct_1 @ 
% 4.12/4.32               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 4.12/4.32          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 4.12/4.32          | ~ (v1_funct_1 @ sk_D))),
% 4.12/4.32      inference('sup-', [status(thm)], ['33', '34'])).
% 4.12/4.32  thf('36', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('38', plain,
% 4.12/4.32      (![X0 : $i, X1 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X0)
% 4.12/4.32          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 4.12/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 4.12/4.32          | ((sk_A) = (k1_xboole_0))
% 4.12/4.32          | (v2_funct_1 @ X0)
% 4.12/4.32          | ~ (v2_funct_1 @ 
% 4.12/4.32               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 4.12/4.32      inference('demod', [status(thm)], ['35', '36', '37'])).
% 4.12/4.32  thf('39', plain,
% 4.12/4.32      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 4.12/4.32        | (v2_funct_1 @ sk_C)
% 4.12/4.32        | ((sk_A) = (k1_xboole_0))
% 4.12/4.32        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 4.12/4.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 4.12/4.32        | ~ (v1_funct_1 @ sk_C))),
% 4.12/4.32      inference('sup-', [status(thm)], ['32', '38'])).
% 4.12/4.32  thf('40', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 4.12/4.32      inference('cnf', [status(esa)], [t52_funct_1])).
% 4.12/4.32  thf('41', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('44', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.12/4.32      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 4.12/4.32  thf('45', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('split', [status(esa)], ['0'])).
% 4.12/4.32  thf('46', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('sup-', [status(thm)], ['44', '45'])).
% 4.12/4.32  thf('47', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(cc1_subset_1, axiom,
% 4.12/4.32    (![A:$i]:
% 4.12/4.32     ( ( v1_xboole_0 @ A ) =>
% 4.12/4.32       ( ![B:$i]:
% 4.12/4.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.12/4.32  thf('48', plain,
% 4.12/4.32      (![X9 : $i, X10 : $i]:
% 4.12/4.32         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 4.12/4.32          | (v1_xboole_0 @ X9)
% 4.12/4.32          | ~ (v1_xboole_0 @ X10))),
% 4.12/4.32      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.12/4.32  thf('49', plain,
% 4.12/4.32      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_xboole_0 @ sk_C))),
% 4.12/4.32      inference('sup-', [status(thm)], ['47', '48'])).
% 4.12/4.32  thf('50', plain,
% 4.12/4.32      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 4.12/4.32         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('sup-', [status(thm)], ['46', '49'])).
% 4.12/4.32  thf(t113_zfmisc_1, axiom,
% 4.12/4.32    (![A:$i,B:$i]:
% 4.12/4.32     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.12/4.32       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.12/4.32  thf('51', plain,
% 4.12/4.32      (![X6 : $i, X7 : $i]:
% 4.12/4.32         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 4.12/4.32      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.12/4.32  thf('52', plain,
% 4.12/4.32      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 4.12/4.32      inference('simplify', [status(thm)], ['51'])).
% 4.12/4.32  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.12/4.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.12/4.32  thf('54', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.12/4.32      inference('demod', [status(thm)], ['50', '52', '53'])).
% 4.12/4.32  thf('55', plain, (((v2_funct_1 @ sk_C))),
% 4.12/4.32      inference('demod', [status(thm)], ['13', '54'])).
% 4.12/4.32  thf('56', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 4.12/4.32      inference('split', [status(esa)], ['0'])).
% 4.12/4.32  thf('57', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.12/4.32      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 4.12/4.32  thf('58', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 4.12/4.32      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 4.12/4.32  thf('59', plain,
% 4.12/4.32      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 4.12/4.32         = (k6_relat_1 @ sk_A))),
% 4.12/4.32      inference('demod', [status(thm)], ['28', '31'])).
% 4.12/4.32  thf('60', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(t24_funct_2, axiom,
% 4.12/4.32    (![A:$i,B:$i,C:$i]:
% 4.12/4.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.12/4.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.32       ( ![D:$i]:
% 4.12/4.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.12/4.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.12/4.32           ( ( r2_relset_1 @
% 4.12/4.32               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.12/4.32               ( k6_partfun1 @ B ) ) =>
% 4.12/4.32             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.12/4.32  thf('61', plain,
% 4.12/4.32      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X40)
% 4.12/4.32          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 4.12/4.32          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 4.12/4.32          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 4.12/4.32               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 4.12/4.32               (k6_partfun1 @ X41))
% 4.12/4.32          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 4.12/4.32          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 4.12/4.32          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 4.12/4.32          | ~ (v1_funct_1 @ X43))),
% 4.12/4.32      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.12/4.32  thf('62', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 4.12/4.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.12/4.32  thf('63', plain,
% 4.12/4.32      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X40)
% 4.12/4.32          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 4.12/4.32          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 4.12/4.32          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 4.12/4.32               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 4.12/4.32               (k6_relat_1 @ X41))
% 4.12/4.32          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 4.12/4.32          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 4.12/4.32          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 4.12/4.32          | ~ (v1_funct_1 @ X43))),
% 4.12/4.32      inference('demod', [status(thm)], ['61', '62'])).
% 4.12/4.32  thf('64', plain,
% 4.12/4.32      (![X0 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X0)
% 4.12/4.32          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 4.12/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 4.12/4.32          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 4.12/4.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.32               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 4.12/4.32               (k6_relat_1 @ sk_A))
% 4.12/4.32          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 4.12/4.32          | ~ (v1_funct_1 @ sk_C))),
% 4.12/4.32      inference('sup-', [status(thm)], ['60', '63'])).
% 4.12/4.32  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('67', plain,
% 4.12/4.32      (![X0 : $i]:
% 4.12/4.32         (~ (v1_funct_1 @ X0)
% 4.12/4.32          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 4.12/4.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 4.12/4.32          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 4.12/4.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.32               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 4.12/4.32               (k6_relat_1 @ sk_A)))),
% 4.12/4.32      inference('demod', [status(thm)], ['64', '65', '66'])).
% 4.12/4.32  thf('68', plain,
% 4.12/4.32      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 4.12/4.32           (k6_relat_1 @ sk_A))
% 4.12/4.32        | ((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 4.12/4.32        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 4.12/4.32        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 4.12/4.32        | ~ (v1_funct_1 @ sk_D))),
% 4.12/4.32      inference('sup-', [status(thm)], ['59', '67'])).
% 4.12/4.32  thf('69', plain,
% 4.12/4.32      (![X38 : $i]:
% 4.12/4.32         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 4.12/4.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 4.12/4.32      inference('demod', [status(thm)], ['29', '30'])).
% 4.12/4.32  thf('70', plain,
% 4.12/4.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.12/4.32         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.12/4.32          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.12/4.32          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 4.12/4.32          | ((X25) != (X28)))),
% 4.12/4.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.12/4.32  thf('71', plain,
% 4.12/4.32      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.12/4.32         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 4.12/4.32          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.12/4.32      inference('simplify', [status(thm)], ['70'])).
% 4.12/4.32  thf('72', plain,
% 4.12/4.32      (![X0 : $i]:
% 4.12/4.32         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 4.12/4.32      inference('sup-', [status(thm)], ['69', '71'])).
% 4.12/4.32  thf('73', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(redefinition_k2_relset_1, axiom,
% 4.12/4.32    (![A:$i,B:$i,C:$i]:
% 4.12/4.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.12/4.32       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.12/4.32  thf('74', plain,
% 4.12/4.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.12/4.32         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 4.12/4.32          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 4.12/4.32      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.12/4.32  thf('75', plain,
% 4.12/4.32      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.12/4.32      inference('sup-', [status(thm)], ['73', '74'])).
% 4.12/4.32  thf('76', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('77', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf('79', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.12/4.32      inference('demod', [status(thm)], ['68', '72', '75', '76', '77', '78'])).
% 4.12/4.32  thf(d3_funct_2, axiom,
% 4.12/4.32    (![A:$i,B:$i]:
% 4.12/4.32     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.12/4.32       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.12/4.32  thf('80', plain,
% 4.12/4.32      (![X29 : $i, X30 : $i]:
% 4.12/4.32         (((k2_relat_1 @ X30) != (X29))
% 4.12/4.32          | (v2_funct_2 @ X30 @ X29)
% 4.12/4.32          | ~ (v5_relat_1 @ X30 @ X29)
% 4.12/4.32          | ~ (v1_relat_1 @ X30))),
% 4.12/4.32      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.12/4.32  thf('81', plain,
% 4.12/4.32      (![X30 : $i]:
% 4.12/4.32         (~ (v1_relat_1 @ X30)
% 4.12/4.32          | ~ (v5_relat_1 @ X30 @ (k2_relat_1 @ X30))
% 4.12/4.32          | (v2_funct_2 @ X30 @ (k2_relat_1 @ X30)))),
% 4.12/4.32      inference('simplify', [status(thm)], ['80'])).
% 4.12/4.32  thf('82', plain,
% 4.12/4.32      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 4.12/4.32        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 4.12/4.32        | ~ (v1_relat_1 @ sk_D))),
% 4.12/4.32      inference('sup-', [status(thm)], ['79', '81'])).
% 4.12/4.32  thf('83', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(cc2_relset_1, axiom,
% 4.12/4.32    (![A:$i,B:$i,C:$i]:
% 4.12/4.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.12/4.32       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.12/4.32  thf('84', plain,
% 4.12/4.32      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.12/4.32         ((v5_relat_1 @ X19 @ X21)
% 4.12/4.32          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.12/4.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.12/4.32  thf('85', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.12/4.32      inference('sup-', [status(thm)], ['83', '84'])).
% 4.12/4.32  thf('86', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.12/4.32      inference('demod', [status(thm)], ['68', '72', '75', '76', '77', '78'])).
% 4.12/4.32  thf('87', plain,
% 4.12/4.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.12/4.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.32  thf(cc2_relat_1, axiom,
% 4.12/4.32    (![A:$i]:
% 4.12/4.32     ( ( v1_relat_1 @ A ) =>
% 4.12/4.32       ( ![B:$i]:
% 4.12/4.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.12/4.32  thf('88', plain,
% 4.12/4.32      (![X14 : $i, X15 : $i]:
% 4.12/4.32         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.12/4.32          | (v1_relat_1 @ X14)
% 4.12/4.32          | ~ (v1_relat_1 @ X15))),
% 4.12/4.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.12/4.32  thf('89', plain,
% 4.12/4.32      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.12/4.32      inference('sup-', [status(thm)], ['87', '88'])).
% 4.12/4.32  thf(fc6_relat_1, axiom,
% 4.12/4.32    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.12/4.32  thf('90', plain,
% 4.12/4.32      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.12/4.32      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.12/4.32  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 4.12/4.32      inference('demod', [status(thm)], ['89', '90'])).
% 4.12/4.32  thf('92', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.12/4.32      inference('demod', [status(thm)], ['82', '85', '86', '91'])).
% 4.12/4.32  thf('93', plain, ($false), inference('demod', [status(thm)], ['58', '92'])).
% 4.12/4.32  
% 4.12/4.32  % SZS output end Refutation
% 4.12/4.32  
% 4.12/4.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
