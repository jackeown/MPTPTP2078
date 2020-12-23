%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HzjMS5BfnA

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:05 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 307 expanded)
%              Number of leaves         :   38 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          : 1158 (5553 expanded)
%              Number of equality atoms :   44 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('18',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('38',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39 ) )
      | ( v2_funct_1 @ X43 )
      | ( X41 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','58','59'])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','60'])).

thf('62',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','63'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('78',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['72','76','79','80','81','82'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('84',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != X26 )
      | ( v2_funct_2 @ X27 @ X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('85',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('89',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['72','76','79','80','81','82'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['86','89','90','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['64','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HzjMS5BfnA
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.33/3.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.33/3.52  % Solved by: fo/fo7.sh
% 3.33/3.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.33/3.52  % done 4257 iterations in 3.064s
% 3.33/3.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.33/3.52  % SZS output start Refutation
% 3.33/3.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.33/3.52  thf(sk_C_type, type, sk_C: $i).
% 3.33/3.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.33/3.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.33/3.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.33/3.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.33/3.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.33/3.52  thf(sk_B_type, type, sk_B: $i).
% 3.33/3.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.33/3.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.33/3.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.33/3.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.33/3.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.33/3.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.33/3.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.33/3.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.33/3.52  thf(sk_D_type, type, sk_D: $i).
% 3.33/3.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.33/3.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.33/3.52  thf(sk_A_type, type, sk_A: $i).
% 3.33/3.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.33/3.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.33/3.52  thf(t29_funct_2, conjecture,
% 3.33/3.52    (![A:$i,B:$i,C:$i]:
% 3.33/3.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.52       ( ![D:$i]:
% 3.33/3.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.33/3.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.33/3.52           ( ( r2_relset_1 @
% 3.33/3.52               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.33/3.52               ( k6_partfun1 @ A ) ) =>
% 3.33/3.52             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.33/3.52  thf(zf_stmt_0, negated_conjecture,
% 3.33/3.52    (~( ![A:$i,B:$i,C:$i]:
% 3.33/3.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.52          ( ![D:$i]:
% 3.33/3.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.33/3.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.33/3.52              ( ( r2_relset_1 @
% 3.33/3.52                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.33/3.52                  ( k6_partfun1 @ A ) ) =>
% 3.33/3.52                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.33/3.52    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.33/3.52  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.33/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.52  thf('1', plain,
% 3.33/3.52      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.33/3.52      inference('split', [status(esa)], ['0'])).
% 3.33/3.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.33/3.52  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.33/3.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.33/3.52  thf(t8_boole, axiom,
% 3.33/3.52    (![A:$i,B:$i]:
% 3.33/3.52     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.33/3.52  thf('3', plain,
% 3.33/3.52      (![X0 : $i, X1 : $i]:
% 3.33/3.52         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.33/3.52      inference('cnf', [status(esa)], [t8_boole])).
% 3.33/3.52  thf('4', plain,
% 3.33/3.52      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.33/3.52      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.52  thf(t113_zfmisc_1, axiom,
% 3.33/3.52    (![A:$i,B:$i]:
% 3.33/3.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.33/3.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.33/3.52  thf('5', plain,
% 3.33/3.52      (![X3 : $i, X4 : $i]:
% 3.33/3.52         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 3.33/3.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.33/3.52  thf('6', plain,
% 3.33/3.52      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 3.33/3.52      inference('simplify', [status(thm)], ['5'])).
% 3.33/3.52  thf(t29_relset_1, axiom,
% 3.33/3.52    (![A:$i]:
% 3.33/3.52     ( m1_subset_1 @
% 3.33/3.52       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.33/3.52  thf('7', plain,
% 3.33/3.52      (![X25 : $i]:
% 3.33/3.52         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 3.33/3.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.33/3.52      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.33/3.52  thf(redefinition_k6_partfun1, axiom,
% 3.33/3.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.33/3.52  thf('8', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.33/3.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.33/3.52  thf('9', plain,
% 3.33/3.52      (![X25 : $i]:
% 3.33/3.52         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 3.33/3.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.33/3.52      inference('demod', [status(thm)], ['7', '8'])).
% 3.33/3.52  thf('10', plain,
% 3.33/3.52      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.33/3.52      inference('sup+', [status(thm)], ['6', '9'])).
% 3.33/3.52  thf(cc1_subset_1, axiom,
% 3.33/3.52    (![A:$i]:
% 3.33/3.52     ( ( v1_xboole_0 @ A ) =>
% 3.33/3.52       ( ![B:$i]:
% 3.33/3.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.33/3.52  thf('11', plain,
% 3.33/3.52      (![X5 : $i, X6 : $i]:
% 3.33/3.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.33/3.52          | (v1_xboole_0 @ X5)
% 3.33/3.52          | ~ (v1_xboole_0 @ X6))),
% 3.33/3.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.33/3.52  thf('12', plain,
% 3.33/3.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.33/3.52        | (v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0)))),
% 3.33/3.52      inference('sup-', [status(thm)], ['10', '11'])).
% 3.33/3.52  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.33/3.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.33/3.52  thf('14', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 3.33/3.52      inference('demod', [status(thm)], ['12', '13'])).
% 3.33/3.52  thf('15', plain,
% 3.33/3.52      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.33/3.52      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.52  thf('16', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 3.33/3.52      inference('sup-', [status(thm)], ['14', '15'])).
% 3.33/3.52  thf(fc4_funct_1, axiom,
% 3.33/3.52    (![A:$i]:
% 3.33/3.52     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.33/3.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.33/3.52  thf('17', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 3.33/3.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.33/3.52  thf('18', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.33/3.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.33/3.52  thf('19', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 3.33/3.52      inference('demod', [status(thm)], ['17', '18'])).
% 3.33/3.52  thf('20', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.33/3.52      inference('sup+', [status(thm)], ['16', '19'])).
% 3.33/3.52  thf('21', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.33/3.52      inference('sup+', [status(thm)], ['4', '20'])).
% 3.33/3.52  thf('22', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.33/3.52      inference('split', [status(esa)], ['0'])).
% 3.33/3.52  thf('23', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.33/3.52      inference('sup-', [status(thm)], ['21', '22'])).
% 3.33/3.52  thf('24', plain,
% 3.33/3.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.33/3.52        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.33/3.52        (k6_partfun1 @ sk_A))),
% 3.33/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.52  thf('25', plain,
% 3.33/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.52  thf('26', plain,
% 3.33/3.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.52  thf(dt_k1_partfun1, axiom,
% 3.33/3.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.33/3.52     ( ( ( v1_funct_1 @ E ) & 
% 3.33/3.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.33/3.52         ( v1_funct_1 @ F ) & 
% 3.33/3.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.33/3.52       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.33/3.52         ( m1_subset_1 @
% 3.33/3.52           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.33/3.52           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.33/3.52  thf('27', plain,
% 3.33/3.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.33/3.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.33/3.52          | ~ (v1_funct_1 @ X28)
% 3.33/3.52          | ~ (v1_funct_1 @ X31)
% 3.33/3.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.33/3.52          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 3.33/3.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 3.33/3.52      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.33/3.52  thf('28', plain,
% 3.33/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.52         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.33/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.33/3.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.33/3.52          | ~ (v1_funct_1 @ X1)
% 3.33/3.52          | ~ (v1_funct_1 @ sk_C))),
% 3.33/3.52      inference('sup-', [status(thm)], ['26', '27'])).
% 3.33/3.52  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.52  thf('30', plain,
% 3.33/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.52         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.33/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.33/3.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.33/3.52          | ~ (v1_funct_1 @ X1))),
% 3.33/3.52      inference('demod', [status(thm)], ['28', '29'])).
% 3.33/3.52  thf('31', plain,
% 3.33/3.52      ((~ (v1_funct_1 @ sk_D)
% 3.33/3.52        | (m1_subset_1 @ 
% 3.33/3.52           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.33/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.33/3.52      inference('sup-', [status(thm)], ['25', '30'])).
% 3.33/3.52  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 3.33/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.52  thf('33', plain,
% 3.33/3.52      ((m1_subset_1 @ 
% 3.33/3.52        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.33/3.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.33/3.52      inference('demod', [status(thm)], ['31', '32'])).
% 3.33/3.52  thf(redefinition_r2_relset_1, axiom,
% 3.33/3.52    (![A:$i,B:$i,C:$i,D:$i]:
% 3.33/3.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.33/3.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.33/3.52  thf('34', plain,
% 3.33/3.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.33/3.52         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.33/3.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.33/3.52          | ((X21) = (X24))
% 3.33/3.52          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 3.33/3.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.33/3.52  thf('35', plain,
% 3.33/3.52      (![X0 : $i]:
% 3.33/3.52         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.33/3.52             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.33/3.52          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.33/3.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.33/3.52      inference('sup-', [status(thm)], ['33', '34'])).
% 3.33/3.52  thf('36', plain,
% 3.33/3.52      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.33/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.33/3.52        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.33/3.52            = (k6_partfun1 @ sk_A)))),
% 3.33/3.52      inference('sup-', [status(thm)], ['24', '35'])).
% 3.33/3.52  thf('37', plain,
% 3.33/3.52      (![X25 : $i]:
% 3.33/3.52         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 3.33/3.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.33/3.52      inference('demod', [status(thm)], ['7', '8'])).
% 3.33/3.52  thf('38', plain,
% 3.33/3.52      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.33/3.52         = (k6_partfun1 @ sk_A))),
% 3.33/3.52      inference('demod', [status(thm)], ['36', '37'])).
% 3.33/3.52  thf('39', plain,
% 3.33/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf(t26_funct_2, axiom,
% 3.33/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.33/3.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.33/3.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.53       ( ![E:$i]:
% 3.33/3.53         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.33/3.53             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.33/3.53           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.33/3.53             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.33/3.53               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.33/3.53  thf('40', plain,
% 3.33/3.53      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.33/3.53         (~ (v1_funct_1 @ X39)
% 3.33/3.53          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.33/3.53          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.33/3.53          | ~ (v2_funct_1 @ (k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39))
% 3.33/3.53          | (v2_funct_1 @ X43)
% 3.33/3.53          | ((X41) = (k1_xboole_0))
% 3.33/3.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 3.33/3.53          | ~ (v1_funct_2 @ X43 @ X42 @ X40)
% 3.33/3.53          | ~ (v1_funct_1 @ X43))),
% 3.33/3.53      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.33/3.53  thf('41', plain,
% 3.33/3.53      (![X0 : $i, X1 : $i]:
% 3.33/3.53         (~ (v1_funct_1 @ X0)
% 3.33/3.53          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.33/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.33/3.53          | ((sk_A) = (k1_xboole_0))
% 3.33/3.53          | (v2_funct_1 @ X0)
% 3.33/3.53          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.33/3.53          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.33/3.53          | ~ (v1_funct_1 @ sk_D))),
% 3.33/3.53      inference('sup-', [status(thm)], ['39', '40'])).
% 3.33/3.53  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('44', plain,
% 3.33/3.53      (![X0 : $i, X1 : $i]:
% 3.33/3.53         (~ (v1_funct_1 @ X0)
% 3.33/3.53          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.33/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.33/3.53          | ((sk_A) = (k1_xboole_0))
% 3.33/3.53          | (v2_funct_1 @ X0)
% 3.33/3.53          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.33/3.53      inference('demod', [status(thm)], ['41', '42', '43'])).
% 3.33/3.53  thf('45', plain,
% 3.33/3.53      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.33/3.53        | (v2_funct_1 @ sk_C)
% 3.33/3.53        | ((sk_A) = (k1_xboole_0))
% 3.33/3.53        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.33/3.53        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.33/3.53        | ~ (v1_funct_1 @ sk_C))),
% 3.33/3.53      inference('sup-', [status(thm)], ['38', '44'])).
% 3.33/3.53  thf('46', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 3.33/3.53      inference('demod', [status(thm)], ['17', '18'])).
% 3.33/3.53  thf('47', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('50', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.33/3.53      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 3.33/3.53  thf('51', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.33/3.53      inference('split', [status(esa)], ['0'])).
% 3.33/3.53  thf('52', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.33/3.53      inference('sup-', [status(thm)], ['50', '51'])).
% 3.33/3.53  thf('53', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('54', plain,
% 3.33/3.53      (![X5 : $i, X6 : $i]:
% 3.33/3.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.33/3.53          | (v1_xboole_0 @ X5)
% 3.33/3.53          | ~ (v1_xboole_0 @ X6))),
% 3.33/3.53      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.33/3.53  thf('55', plain,
% 3.33/3.53      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.33/3.53      inference('sup-', [status(thm)], ['53', '54'])).
% 3.33/3.53  thf('56', plain,
% 3.33/3.53      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 3.33/3.53         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.33/3.53      inference('sup-', [status(thm)], ['52', '55'])).
% 3.33/3.53  thf('57', plain,
% 3.33/3.53      (![X3 : $i, X4 : $i]:
% 3.33/3.53         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.33/3.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.33/3.53  thf('58', plain,
% 3.33/3.53      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.33/3.53      inference('simplify', [status(thm)], ['57'])).
% 3.33/3.53  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.33/3.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.33/3.53  thf('60', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.33/3.53      inference('demod', [status(thm)], ['56', '58', '59'])).
% 3.33/3.53  thf('61', plain, (((v2_funct_1 @ sk_C))),
% 3.33/3.53      inference('demod', [status(thm)], ['23', '60'])).
% 3.33/3.53  thf('62', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.33/3.53      inference('split', [status(esa)], ['0'])).
% 3.33/3.53  thf('63', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.33/3.53      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 3.33/3.53  thf('64', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.33/3.53      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 3.33/3.53  thf('65', plain,
% 3.33/3.53      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.33/3.53         = (k6_partfun1 @ sk_A))),
% 3.33/3.53      inference('demod', [status(thm)], ['36', '37'])).
% 3.33/3.53  thf('66', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf(t24_funct_2, axiom,
% 3.33/3.53    (![A:$i,B:$i,C:$i]:
% 3.33/3.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.33/3.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.33/3.53       ( ![D:$i]:
% 3.33/3.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.33/3.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.33/3.53           ( ( r2_relset_1 @
% 3.33/3.53               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.33/3.53               ( k6_partfun1 @ B ) ) =>
% 3.33/3.53             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.33/3.53  thf('67', plain,
% 3.33/3.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.33/3.53         (~ (v1_funct_1 @ X35)
% 3.33/3.53          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.33/3.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.33/3.53          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 3.33/3.53               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 3.33/3.53               (k6_partfun1 @ X36))
% 3.33/3.53          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 3.33/3.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.33/3.53          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.33/3.53          | ~ (v1_funct_1 @ X38))),
% 3.33/3.53      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.33/3.53  thf('68', plain,
% 3.33/3.53      (![X0 : $i]:
% 3.33/3.53         (~ (v1_funct_1 @ X0)
% 3.33/3.53          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.33/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.33/3.53          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.33/3.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.33/3.53               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.33/3.53               (k6_partfun1 @ sk_A))
% 3.33/3.53          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.33/3.53          | ~ (v1_funct_1 @ sk_C))),
% 3.33/3.53      inference('sup-', [status(thm)], ['66', '67'])).
% 3.33/3.53  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('71', plain,
% 3.33/3.53      (![X0 : $i]:
% 3.33/3.53         (~ (v1_funct_1 @ X0)
% 3.33/3.53          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.33/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.33/3.53          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.33/3.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.33/3.53               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.33/3.53               (k6_partfun1 @ sk_A)))),
% 3.33/3.53      inference('demod', [status(thm)], ['68', '69', '70'])).
% 3.33/3.53  thf('72', plain,
% 3.33/3.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 3.33/3.53           (k6_partfun1 @ sk_A))
% 3.33/3.53        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.33/3.53        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.33/3.53        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.33/3.53        | ~ (v1_funct_1 @ sk_D))),
% 3.33/3.53      inference('sup-', [status(thm)], ['65', '71'])).
% 3.33/3.53  thf('73', plain,
% 3.33/3.53      (![X25 : $i]:
% 3.33/3.53         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 3.33/3.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 3.33/3.53      inference('demod', [status(thm)], ['7', '8'])).
% 3.33/3.53  thf('74', plain,
% 3.33/3.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.33/3.53         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.33/3.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.33/3.53          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 3.33/3.53          | ((X21) != (X24)))),
% 3.33/3.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.33/3.53  thf('75', plain,
% 3.33/3.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.33/3.53         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 3.33/3.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.33/3.53      inference('simplify', [status(thm)], ['74'])).
% 3.33/3.53  thf('76', plain,
% 3.33/3.53      (![X0 : $i]:
% 3.33/3.53         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 3.33/3.53      inference('sup-', [status(thm)], ['73', '75'])).
% 3.33/3.53  thf('77', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf(redefinition_k2_relset_1, axiom,
% 3.33/3.53    (![A:$i,B:$i,C:$i]:
% 3.33/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.33/3.53  thf('78', plain,
% 3.33/3.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.33/3.53         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 3.33/3.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.33/3.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.33/3.53  thf('79', plain,
% 3.33/3.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.33/3.53      inference('sup-', [status(thm)], ['77', '78'])).
% 3.33/3.53  thf('80', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('81', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf('83', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.33/3.53      inference('demod', [status(thm)], ['72', '76', '79', '80', '81', '82'])).
% 3.33/3.53  thf(d3_funct_2, axiom,
% 3.33/3.53    (![A:$i,B:$i]:
% 3.33/3.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.33/3.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.33/3.53  thf('84', plain,
% 3.33/3.53      (![X26 : $i, X27 : $i]:
% 3.33/3.53         (((k2_relat_1 @ X27) != (X26))
% 3.33/3.53          | (v2_funct_2 @ X27 @ X26)
% 3.33/3.53          | ~ (v5_relat_1 @ X27 @ X26)
% 3.33/3.53          | ~ (v1_relat_1 @ X27))),
% 3.33/3.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.33/3.53  thf('85', plain,
% 3.33/3.53      (![X27 : $i]:
% 3.33/3.53         (~ (v1_relat_1 @ X27)
% 3.33/3.53          | ~ (v5_relat_1 @ X27 @ (k2_relat_1 @ X27))
% 3.33/3.53          | (v2_funct_2 @ X27 @ (k2_relat_1 @ X27)))),
% 3.33/3.53      inference('simplify', [status(thm)], ['84'])).
% 3.33/3.53  thf('86', plain,
% 3.33/3.53      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.33/3.53        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.33/3.53        | ~ (v1_relat_1 @ sk_D))),
% 3.33/3.53      inference('sup-', [status(thm)], ['83', '85'])).
% 3.33/3.53  thf('87', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf(cc2_relset_1, axiom,
% 3.33/3.53    (![A:$i,B:$i,C:$i]:
% 3.33/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.33/3.53  thf('88', plain,
% 3.33/3.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.33/3.53         ((v5_relat_1 @ X15 @ X17)
% 3.33/3.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.33/3.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.33/3.53  thf('89', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.33/3.53      inference('sup-', [status(thm)], ['87', '88'])).
% 3.33/3.53  thf('90', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.33/3.53      inference('demod', [status(thm)], ['72', '76', '79', '80', '81', '82'])).
% 3.33/3.53  thf('91', plain,
% 3.33/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.33/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.53  thf(cc1_relset_1, axiom,
% 3.33/3.53    (![A:$i,B:$i,C:$i]:
% 3.33/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.33/3.53       ( v1_relat_1 @ C ) ))).
% 3.33/3.53  thf('92', plain,
% 3.33/3.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.33/3.53         ((v1_relat_1 @ X12)
% 3.33/3.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.33/3.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.33/3.53  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 3.33/3.53      inference('sup-', [status(thm)], ['91', '92'])).
% 3.33/3.53  thf('94', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.33/3.53      inference('demod', [status(thm)], ['86', '89', '90', '93'])).
% 3.33/3.53  thf('95', plain, ($false), inference('demod', [status(thm)], ['64', '94'])).
% 3.33/3.53  
% 3.33/3.53  % SZS output end Refutation
% 3.33/3.53  
% 3.33/3.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
