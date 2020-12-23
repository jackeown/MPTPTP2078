%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6vc3blZz92

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:09 EST 2020

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 315 expanded)
%              Number of leaves         :   38 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          : 1176 (5628 expanded)
%              Number of equality atoms :   45 (  94 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('11',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('18',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','20'])).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
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
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
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
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('60',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','60','61'])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','62'])).

thf('64',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','65'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('80',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['74','78','81','82','83','84'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('87',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['74','78','81','82','83','84'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['88','91','92','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['66','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6vc3blZz92
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.71/2.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.71/2.91  % Solved by: fo/fo7.sh
% 2.71/2.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.71/2.91  % done 3440 iterations in 2.458s
% 2.71/2.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.71/2.91  % SZS output start Refutation
% 2.71/2.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.71/2.91  thf(sk_D_type, type, sk_D: $i).
% 2.71/2.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.71/2.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.71/2.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.71/2.91  thf(sk_B_type, type, sk_B: $i).
% 2.71/2.91  thf(sk_A_type, type, sk_A: $i).
% 2.71/2.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.71/2.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.71/2.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.71/2.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.71/2.91  thf(sk_C_type, type, sk_C: $i).
% 2.71/2.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.71/2.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.71/2.91  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.71/2.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.71/2.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.71/2.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.71/2.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.71/2.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.71/2.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.71/2.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.71/2.91  thf(t29_funct_2, conjecture,
% 2.71/2.91    (![A:$i,B:$i,C:$i]:
% 2.71/2.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.71/2.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.91       ( ![D:$i]:
% 2.71/2.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.71/2.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.71/2.91           ( ( r2_relset_1 @
% 2.71/2.91               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.71/2.91               ( k6_partfun1 @ A ) ) =>
% 2.71/2.91             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.71/2.91  thf(zf_stmt_0, negated_conjecture,
% 2.71/2.91    (~( ![A:$i,B:$i,C:$i]:
% 2.71/2.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.71/2.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.91          ( ![D:$i]:
% 2.71/2.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.71/2.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.71/2.91              ( ( r2_relset_1 @
% 2.71/2.91                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.71/2.91                  ( k6_partfun1 @ A ) ) =>
% 2.71/2.91                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.71/2.91    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.71/2.91  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('1', plain,
% 2.71/2.91      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.71/2.91      inference('split', [status(esa)], ['0'])).
% 2.71/2.91  thf(l13_xboole_0, axiom,
% 2.71/2.91    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.71/2.91  thf('2', plain,
% 2.71/2.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.71/2.91      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.71/2.91  thf(t113_zfmisc_1, axiom,
% 2.71/2.91    (![A:$i,B:$i]:
% 2.71/2.91     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.71/2.91       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.71/2.91  thf('3', plain,
% 2.71/2.91      (![X2 : $i, X3 : $i]:
% 2.71/2.91         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.71/2.91      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.71/2.91  thf('4', plain,
% 2.71/2.91      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.71/2.91      inference('simplify', [status(thm)], ['3'])).
% 2.71/2.91  thf(t29_relset_1, axiom,
% 2.71/2.91    (![A:$i]:
% 2.71/2.91     ( m1_subset_1 @
% 2.71/2.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.71/2.91  thf('5', plain,
% 2.71/2.91      (![X22 : $i]:
% 2.71/2.91         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 2.71/2.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.71/2.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.71/2.91  thf(redefinition_k6_partfun1, axiom,
% 2.71/2.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.71/2.91  thf('6', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.71/2.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.71/2.91  thf('7', plain,
% 2.71/2.91      (![X22 : $i]:
% 2.71/2.91         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 2.71/2.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.71/2.91      inference('demod', [status(thm)], ['5', '6'])).
% 2.71/2.91  thf('8', plain,
% 2.71/2.91      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.71/2.91      inference('sup+', [status(thm)], ['4', '7'])).
% 2.71/2.91  thf('9', plain,
% 2.71/2.91      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.71/2.91      inference('simplify', [status(thm)], ['3'])).
% 2.71/2.91  thf(cc4_relset_1, axiom,
% 2.71/2.91    (![A:$i,B:$i]:
% 2.71/2.91     ( ( v1_xboole_0 @ A ) =>
% 2.71/2.91       ( ![C:$i]:
% 2.71/2.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.71/2.91           ( v1_xboole_0 @ C ) ) ) ))).
% 2.71/2.91  thf('10', plain,
% 2.71/2.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.71/2.91         (~ (v1_xboole_0 @ X12)
% 2.71/2.91          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 2.71/2.91          | (v1_xboole_0 @ X13))),
% 2.71/2.91      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.71/2.91  thf('11', plain,
% 2.71/2.91      (![X1 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.71/2.91          | (v1_xboole_0 @ X1)
% 2.71/2.91          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['9', '10'])).
% 2.71/2.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.71/2.91  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.71/2.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.71/2.91  thf('13', plain,
% 2.71/2.91      (![X1 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.71/2.91          | (v1_xboole_0 @ X1))),
% 2.71/2.91      inference('demod', [status(thm)], ['11', '12'])).
% 2.71/2.91  thf('14', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['8', '13'])).
% 2.71/2.91  thf('15', plain,
% 2.71/2.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.71/2.91      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.71/2.91  thf('16', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['14', '15'])).
% 2.71/2.91  thf(fc4_funct_1, axiom,
% 2.71/2.91    (![A:$i]:
% 2.71/2.91     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.71/2.91       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.71/2.91  thf('17', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.71/2.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.71/2.91  thf('18', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.71/2.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.71/2.91  thf('19', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 2.71/2.91      inference('demod', [status(thm)], ['17', '18'])).
% 2.71/2.91  thf('20', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.71/2.91      inference('sup+', [status(thm)], ['16', '19'])).
% 2.71/2.91  thf('21', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.71/2.91      inference('sup+', [status(thm)], ['2', '20'])).
% 2.71/2.91  thf('22', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.91      inference('split', [status(esa)], ['0'])).
% 2.71/2.91  thf('23', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.91      inference('sup-', [status(thm)], ['21', '22'])).
% 2.71/2.91  thf('24', plain,
% 2.71/2.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.91        (k6_partfun1 @ sk_A))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('25', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('26', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf(dt_k1_partfun1, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.71/2.91     ( ( ( v1_funct_1 @ E ) & 
% 2.71/2.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.71/2.91         ( v1_funct_1 @ F ) & 
% 2.71/2.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.71/2.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.71/2.91         ( m1_subset_1 @
% 2.71/2.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.71/2.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.71/2.91  thf('27', plain,
% 2.71/2.91      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.71/2.91          | ~ (v1_funct_1 @ X25)
% 2.71/2.91          | ~ (v1_funct_1 @ X28)
% 2.71/2.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.71/2.91          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 2.71/2.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 2.71/2.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.71/2.91  thf('28', plain,
% 2.71/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.71/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.71/2.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.71/2.91          | ~ (v1_funct_1 @ X1)
% 2.71/2.91          | ~ (v1_funct_1 @ sk_C))),
% 2.71/2.91      inference('sup-', [status(thm)], ['26', '27'])).
% 2.71/2.91  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('30', plain,
% 2.71/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.71/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.71/2.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.71/2.91          | ~ (v1_funct_1 @ X1))),
% 2.71/2.91      inference('demod', [status(thm)], ['28', '29'])).
% 2.71/2.91  thf('31', plain,
% 2.71/2.91      ((~ (v1_funct_1 @ sk_D)
% 2.71/2.91        | (m1_subset_1 @ 
% 2.71/2.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.71/2.91      inference('sup-', [status(thm)], ['25', '30'])).
% 2.71/2.91  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('33', plain,
% 2.71/2.91      ((m1_subset_1 @ 
% 2.71/2.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.71/2.91      inference('demod', [status(thm)], ['31', '32'])).
% 2.71/2.91  thf(redefinition_r2_relset_1, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i,D:$i]:
% 2.71/2.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.71/2.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.71/2.91  thf('34', plain,
% 2.71/2.91      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.71/2.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.71/2.91          | ((X18) = (X21))
% 2.71/2.91          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.71/2.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.71/2.91  thf('35', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.91             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.71/2.91          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.71/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.71/2.91      inference('sup-', [status(thm)], ['33', '34'])).
% 2.71/2.91  thf('36', plain,
% 2.71/2.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.71/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.71/2.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.91            = (k6_partfun1 @ sk_A)))),
% 2.71/2.91      inference('sup-', [status(thm)], ['24', '35'])).
% 2.71/2.91  thf('37', plain,
% 2.71/2.91      (![X22 : $i]:
% 2.71/2.91         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 2.71/2.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.71/2.91      inference('demod', [status(thm)], ['5', '6'])).
% 2.71/2.91  thf('38', plain,
% 2.71/2.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.91         = (k6_partfun1 @ sk_A))),
% 2.71/2.91      inference('demod', [status(thm)], ['36', '37'])).
% 2.71/2.91  thf('39', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf(t26_funct_2, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i,D:$i]:
% 2.71/2.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.71/2.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.91       ( ![E:$i]:
% 2.71/2.91         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.71/2.91             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.71/2.91           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.71/2.91             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.71/2.91               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.71/2.91  thf('40', plain,
% 2.71/2.91      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.71/2.91         (~ (v1_funct_1 @ X36)
% 2.71/2.91          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.71/2.91          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.71/2.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 2.71/2.91          | (v2_funct_1 @ X40)
% 2.71/2.91          | ((X38) = (k1_xboole_0))
% 2.71/2.91          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 2.71/2.91          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 2.71/2.91          | ~ (v1_funct_1 @ X40))),
% 2.71/2.91      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.71/2.91  thf('41', plain,
% 2.71/2.91      (![X0 : $i, X1 : $i]:
% 2.71/2.91         (~ (v1_funct_1 @ X0)
% 2.71/2.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.71/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.71/2.91          | ((sk_A) = (k1_xboole_0))
% 2.71/2.91          | (v2_funct_1 @ X0)
% 2.71/2.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.71/2.91          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.71/2.91          | ~ (v1_funct_1 @ sk_D))),
% 2.71/2.91      inference('sup-', [status(thm)], ['39', '40'])).
% 2.71/2.91  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('44', plain,
% 2.71/2.91      (![X0 : $i, X1 : $i]:
% 2.71/2.91         (~ (v1_funct_1 @ X0)
% 2.71/2.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.71/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.71/2.91          | ((sk_A) = (k1_xboole_0))
% 2.71/2.91          | (v2_funct_1 @ X0)
% 2.71/2.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.71/2.91      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.71/2.91  thf('45', plain,
% 2.71/2.91      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.71/2.91        | (v2_funct_1 @ sk_C)
% 2.71/2.91        | ((sk_A) = (k1_xboole_0))
% 2.71/2.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.71/2.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.71/2.91        | ~ (v1_funct_1 @ sk_C))),
% 2.71/2.91      inference('sup-', [status(thm)], ['38', '44'])).
% 2.71/2.91  thf('46', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 2.71/2.91      inference('demod', [status(thm)], ['17', '18'])).
% 2.71/2.91  thf('47', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('50', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.71/2.91      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 2.71/2.91  thf('51', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.91      inference('split', [status(esa)], ['0'])).
% 2.71/2.91  thf('52', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.91      inference('sup-', [status(thm)], ['50', '51'])).
% 2.71/2.91  thf('53', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('54', plain,
% 2.71/2.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.71/2.91      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.71/2.91  thf('55', plain,
% 2.71/2.91      (![X1 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.71/2.91          | (v1_xboole_0 @ X1))),
% 2.71/2.91      inference('demod', [status(thm)], ['11', '12'])).
% 2.71/2.91  thf('56', plain,
% 2.71/2.91      (![X0 : $i, X1 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 2.71/2.91          | ~ (v1_xboole_0 @ X0)
% 2.71/2.91          | (v1_xboole_0 @ X1))),
% 2.71/2.91      inference('sup-', [status(thm)], ['54', '55'])).
% 2.71/2.91  thf('57', plain,
% 2.71/2.91      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.91      inference('sup-', [status(thm)], ['53', '56'])).
% 2.71/2.91  thf('58', plain,
% 2.71/2.91      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 2.71/2.91         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.91      inference('sup-', [status(thm)], ['52', '57'])).
% 2.71/2.91  thf('59', plain,
% 2.71/2.91      (![X2 : $i, X3 : $i]:
% 2.71/2.91         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 2.71/2.91      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.71/2.91  thf('60', plain,
% 2.71/2.91      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.71/2.91      inference('simplify', [status(thm)], ['59'])).
% 2.71/2.91  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.71/2.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.71/2.91  thf('62', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.91      inference('demod', [status(thm)], ['58', '60', '61'])).
% 2.71/2.91  thf('63', plain, (((v2_funct_1 @ sk_C))),
% 2.71/2.91      inference('demod', [status(thm)], ['23', '62'])).
% 2.71/2.91  thf('64', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 2.71/2.91      inference('split', [status(esa)], ['0'])).
% 2.71/2.91  thf('65', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.71/2.91      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 2.71/2.91  thf('66', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 2.71/2.91      inference('simpl_trail', [status(thm)], ['1', '65'])).
% 2.71/2.91  thf('67', plain,
% 2.71/2.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.91         = (k6_partfun1 @ sk_A))),
% 2.71/2.91      inference('demod', [status(thm)], ['36', '37'])).
% 2.71/2.91  thf('68', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf(t24_funct_2, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i]:
% 2.71/2.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.71/2.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.91       ( ![D:$i]:
% 2.71/2.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.71/2.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.71/2.91           ( ( r2_relset_1 @
% 2.71/2.91               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.71/2.91               ( k6_partfun1 @ B ) ) =>
% 2.71/2.91             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.71/2.91  thf('69', plain,
% 2.71/2.91      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.71/2.91         (~ (v1_funct_1 @ X32)
% 2.71/2.91          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 2.71/2.91          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.71/2.91          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 2.71/2.91               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 2.71/2.91               (k6_partfun1 @ X33))
% 2.71/2.91          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 2.71/2.91          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 2.71/2.91          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 2.71/2.91          | ~ (v1_funct_1 @ X35))),
% 2.71/2.91      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.71/2.91  thf('70', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         (~ (v1_funct_1 @ X0)
% 2.71/2.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.71/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.71/2.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.71/2.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.71/2.91               (k6_partfun1 @ sk_A))
% 2.71/2.91          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.71/2.91          | ~ (v1_funct_1 @ sk_C))),
% 2.71/2.91      inference('sup-', [status(thm)], ['68', '69'])).
% 2.71/2.91  thf('71', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('73', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         (~ (v1_funct_1 @ X0)
% 2.71/2.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.71/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.71/2.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.71/2.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.71/2.91               (k6_partfun1 @ sk_A)))),
% 2.71/2.91      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.71/2.91  thf('74', plain,
% 2.71/2.91      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 2.71/2.91           (k6_partfun1 @ sk_A))
% 2.71/2.91        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.71/2.91        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.71/2.91        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.71/2.91        | ~ (v1_funct_1 @ sk_D))),
% 2.71/2.91      inference('sup-', [status(thm)], ['67', '73'])).
% 2.71/2.91  thf('75', plain,
% 2.71/2.91      (![X22 : $i]:
% 2.71/2.91         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 2.71/2.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.71/2.91      inference('demod', [status(thm)], ['5', '6'])).
% 2.71/2.91  thf('76', plain,
% 2.71/2.91      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.71/2.91         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.71/2.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.71/2.91          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 2.71/2.91          | ((X18) != (X21)))),
% 2.71/2.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.71/2.91  thf('77', plain,
% 2.71/2.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.71/2.91         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 2.71/2.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.71/2.91      inference('simplify', [status(thm)], ['76'])).
% 2.71/2.91  thf('78', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['75', '77'])).
% 2.71/2.91  thf('79', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf(redefinition_k2_relset_1, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i]:
% 2.71/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.71/2.91  thf('80', plain,
% 2.71/2.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.71/2.91         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.71/2.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.71/2.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.71/2.91  thf('81', plain,
% 2.71/2.91      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.71/2.91      inference('sup-', [status(thm)], ['79', '80'])).
% 2.71/2.91  thf('82', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('83', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('85', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.71/2.91      inference('demod', [status(thm)], ['74', '78', '81', '82', '83', '84'])).
% 2.71/2.91  thf(d3_funct_2, axiom,
% 2.71/2.91    (![A:$i,B:$i]:
% 2.71/2.91     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.71/2.91       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.71/2.91  thf('86', plain,
% 2.71/2.91      (![X23 : $i, X24 : $i]:
% 2.71/2.91         (((k2_relat_1 @ X24) != (X23))
% 2.71/2.91          | (v2_funct_2 @ X24 @ X23)
% 2.71/2.91          | ~ (v5_relat_1 @ X24 @ X23)
% 2.71/2.91          | ~ (v1_relat_1 @ X24))),
% 2.71/2.91      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.71/2.91  thf('87', plain,
% 2.71/2.91      (![X24 : $i]:
% 2.71/2.91         (~ (v1_relat_1 @ X24)
% 2.71/2.91          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 2.71/2.91          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 2.71/2.91      inference('simplify', [status(thm)], ['86'])).
% 2.71/2.91  thf('88', plain,
% 2.71/2.91      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.71/2.91        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.71/2.91        | ~ (v1_relat_1 @ sk_D))),
% 2.71/2.91      inference('sup-', [status(thm)], ['85', '87'])).
% 2.71/2.91  thf('89', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf(cc2_relset_1, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i]:
% 2.71/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.71/2.91  thf('90', plain,
% 2.71/2.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.71/2.91         ((v5_relat_1 @ X9 @ X11)
% 2.71/2.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.71/2.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.71/2.91  thf('91', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.71/2.91      inference('sup-', [status(thm)], ['89', '90'])).
% 2.71/2.91  thf('92', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.71/2.91      inference('demod', [status(thm)], ['74', '78', '81', '82', '83', '84'])).
% 2.71/2.91  thf('93', plain,
% 2.71/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf(cc1_relset_1, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i]:
% 2.71/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.91       ( v1_relat_1 @ C ) ))).
% 2.71/2.91  thf('94', plain,
% 2.71/2.91      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.71/2.91         ((v1_relat_1 @ X6)
% 2.71/2.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.71/2.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.71/2.91  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.71/2.91      inference('sup-', [status(thm)], ['93', '94'])).
% 2.71/2.91  thf('96', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.71/2.91      inference('demod', [status(thm)], ['88', '91', '92', '95'])).
% 2.71/2.91  thf('97', plain, ($false), inference('demod', [status(thm)], ['66', '96'])).
% 2.71/2.91  
% 2.71/2.91  % SZS output end Refutation
% 2.71/2.91  
% 2.71/2.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
