%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhHfdNb89B

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:21 EST 2020

% Result     : Theorem 6.79s
% Output     : Refutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 335 expanded)
%              Number of leaves         :   46 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          : 1234 (5310 expanded)
%              Number of equality atoms :   51 (  89 expanded)
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

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('5',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('21',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','23'])).

thf('25',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48 ) )
      | ( v2_funct_1 @ X52 )
      | ( X50 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X49 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('61',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','61','62'])).

thf('64',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','63'])).

thf('65',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('77',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('79',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('82',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('91',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('93',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('97',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['81','84','95','96','97','98','103'])).

thf('105',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('106',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('108',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
       != X33 )
      | ( v2_funct_2 @ X34 @ X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('109',plain,(
    ! [X34: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ~ ( v5_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
      | ( v2_funct_2 @ X34 @ ( k2_relat_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['104','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('114',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['67','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhHfdNb89B
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.79/7.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.79/7.02  % Solved by: fo/fo7.sh
% 6.79/7.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.79/7.02  % done 5438 iterations in 6.548s
% 6.79/7.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.79/7.02  % SZS output start Refutation
% 6.79/7.02  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.79/7.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.79/7.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.79/7.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.79/7.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.79/7.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.79/7.02  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.79/7.02  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.79/7.02  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 6.79/7.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.79/7.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.79/7.02  thf(sk_D_type, type, sk_D: $i).
% 6.79/7.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.79/7.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.79/7.02  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.79/7.02  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.79/7.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.79/7.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.79/7.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.79/7.02  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.79/7.02  thf(sk_B_type, type, sk_B: $i).
% 6.79/7.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.79/7.02  thf(sk_A_type, type, sk_A: $i).
% 6.79/7.02  thf(sk_C_type, type, sk_C: $i).
% 6.79/7.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.79/7.02  thf(t29_funct_2, conjecture,
% 6.79/7.02    (![A:$i,B:$i,C:$i]:
% 6.79/7.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.79/7.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.79/7.02       ( ![D:$i]:
% 6.79/7.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.79/7.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.79/7.02           ( ( r2_relset_1 @
% 6.79/7.02               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.79/7.02               ( k6_partfun1 @ A ) ) =>
% 6.79/7.02             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 6.79/7.02  thf(zf_stmt_0, negated_conjecture,
% 6.79/7.02    (~( ![A:$i,B:$i,C:$i]:
% 6.79/7.02        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.79/7.02            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.79/7.02          ( ![D:$i]:
% 6.79/7.02            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.79/7.02                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.79/7.02              ( ( r2_relset_1 @
% 6.79/7.02                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.79/7.02                  ( k6_partfun1 @ A ) ) =>
% 6.79/7.02                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 6.79/7.02    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 6.79/7.02  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 6.79/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.02  thf('1', plain,
% 6.79/7.02      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 6.79/7.02      inference('split', [status(esa)], ['0'])).
% 6.79/7.02  thf(l13_xboole_0, axiom,
% 6.79/7.02    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.79/7.02  thf('2', plain,
% 6.79/7.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.79/7.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.79/7.02  thf(t113_zfmisc_1, axiom,
% 6.79/7.02    (![A:$i,B:$i]:
% 6.79/7.02     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.79/7.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.79/7.02  thf('3', plain,
% 6.79/7.02      (![X9 : $i, X10 : $i]:
% 6.79/7.02         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 6.79/7.02      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.79/7.02  thf('4', plain,
% 6.79/7.02      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 6.79/7.02      inference('simplify', [status(thm)], ['3'])).
% 6.79/7.02  thf(t29_relset_1, axiom,
% 6.79/7.02    (![A:$i]:
% 6.79/7.02     ( m1_subset_1 @
% 6.79/7.02       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 6.79/7.02  thf('5', plain,
% 6.79/7.02      (![X32 : $i]:
% 6.79/7.02         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 6.79/7.02          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 6.79/7.02      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.79/7.02  thf(redefinition_k6_partfun1, axiom,
% 6.79/7.02    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.79/7.02  thf('6', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 6.79/7.02      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.79/7.02  thf('7', plain,
% 6.79/7.02      (![X32 : $i]:
% 6.79/7.02         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 6.79/7.02          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 6.79/7.02      inference('demod', [status(thm)], ['5', '6'])).
% 6.79/7.02  thf('8', plain,
% 6.79/7.02      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 6.79/7.02      inference('sup+', [status(thm)], ['4', '7'])).
% 6.79/7.02  thf(cc1_subset_1, axiom,
% 6.79/7.02    (![A:$i]:
% 6.79/7.02     ( ( v1_xboole_0 @ A ) =>
% 6.79/7.02       ( ![B:$i]:
% 6.79/7.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 6.79/7.02  thf('9', plain,
% 6.79/7.02      (![X11 : $i, X12 : $i]:
% 6.79/7.02         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.79/7.02          | (v1_xboole_0 @ X11)
% 6.79/7.02          | ~ (v1_xboole_0 @ X12))),
% 6.79/7.02      inference('cnf', [status(esa)], [cc1_subset_1])).
% 6.79/7.02  thf('10', plain,
% 6.79/7.02      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.79/7.02        | (v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0)))),
% 6.79/7.02      inference('sup-', [status(thm)], ['8', '9'])).
% 6.79/7.02  thf(d10_xboole_0, axiom,
% 6.79/7.02    (![A:$i,B:$i]:
% 6.79/7.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.79/7.02  thf('11', plain,
% 6.79/7.02      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 6.79/7.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.79/7.02  thf('12', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 6.79/7.02      inference('simplify', [status(thm)], ['11'])).
% 6.79/7.02  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 6.79/7.02  thf('13', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 6.79/7.02      inference('cnf', [status(esa)], [t65_xboole_1])).
% 6.79/7.02  thf(t69_xboole_1, axiom,
% 6.79/7.02    (![A:$i,B:$i]:
% 6.79/7.02     ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.79/7.02       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 6.79/7.02  thf('14', plain,
% 6.79/7.02      (![X6 : $i, X7 : $i]:
% 6.79/7.02         (~ (r1_xboole_0 @ X6 @ X7)
% 6.79/7.02          | ~ (r1_tarski @ X6 @ X7)
% 6.79/7.02          | (v1_xboole_0 @ X6))),
% 6.79/7.02      inference('cnf', [status(esa)], [t69_xboole_1])).
% 6.79/7.02  thf('15', plain,
% 6.79/7.02      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 6.79/7.02      inference('sup-', [status(thm)], ['13', '14'])).
% 6.79/7.02  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.79/7.02      inference('sup-', [status(thm)], ['12', '15'])).
% 6.79/7.02  thf('17', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 6.79/7.02      inference('demod', [status(thm)], ['10', '16'])).
% 6.79/7.02  thf('18', plain,
% 6.79/7.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.79/7.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.79/7.02  thf('19', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.79/7.02      inference('sup-', [status(thm)], ['17', '18'])).
% 6.79/7.02  thf(fc4_funct_1, axiom,
% 6.79/7.02    (![A:$i]:
% 6.79/7.02     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.79/7.02       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.79/7.02  thf('20', plain, (![X24 : $i]: (v2_funct_1 @ (k6_relat_1 @ X24))),
% 6.79/7.02      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.79/7.02  thf('21', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 6.79/7.02      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.79/7.02  thf('22', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 6.79/7.02      inference('demod', [status(thm)], ['20', '21'])).
% 6.79/7.02  thf('23', plain, ((v2_funct_1 @ k1_xboole_0)),
% 6.79/7.02      inference('sup+', [status(thm)], ['19', '22'])).
% 6.79/7.02  thf('24', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.79/7.02      inference('sup+', [status(thm)], ['2', '23'])).
% 6.79/7.02  thf('25', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.79/7.02      inference('split', [status(esa)], ['0'])).
% 6.79/7.02  thf('26', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.79/7.02      inference('sup-', [status(thm)], ['24', '25'])).
% 6.79/7.02  thf('27', plain,
% 6.79/7.02      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.79/7.02        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.79/7.02        (k6_partfun1 @ sk_A))),
% 6.79/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.02  thf('28', plain,
% 6.79/7.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.79/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.02  thf('29', plain,
% 6.79/7.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.79/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.02  thf(dt_k1_partfun1, axiom,
% 6.79/7.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.79/7.02     ( ( ( v1_funct_1 @ E ) & 
% 6.79/7.02         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.79/7.02         ( v1_funct_1 @ F ) & 
% 6.79/7.02         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.79/7.02       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.79/7.02         ( m1_subset_1 @
% 6.79/7.02           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.79/7.02           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.79/7.02  thf('30', plain,
% 6.79/7.02      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 6.79/7.02         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.79/7.02          | ~ (v1_funct_1 @ X35)
% 6.79/7.02          | ~ (v1_funct_1 @ X38)
% 6.79/7.02          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 6.79/7.02          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 6.79/7.02             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 6.79/7.02      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.79/7.02  thf('31', plain,
% 6.79/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.02         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.79/7.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.79/7.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.79/7.03          | ~ (v1_funct_1 @ X1)
% 6.79/7.03          | ~ (v1_funct_1 @ sk_C))),
% 6.79/7.03      inference('sup-', [status(thm)], ['29', '30'])).
% 6.79/7.03  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('33', plain,
% 6.79/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.79/7.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.79/7.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.79/7.03          | ~ (v1_funct_1 @ X1))),
% 6.79/7.03      inference('demod', [status(thm)], ['31', '32'])).
% 6.79/7.03  thf('34', plain,
% 6.79/7.03      ((~ (v1_funct_1 @ sk_D)
% 6.79/7.03        | (m1_subset_1 @ 
% 6.79/7.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.79/7.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.79/7.03      inference('sup-', [status(thm)], ['28', '33'])).
% 6.79/7.03  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('36', plain,
% 6.79/7.03      ((m1_subset_1 @ 
% 6.79/7.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.79/7.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.79/7.03      inference('demod', [status(thm)], ['34', '35'])).
% 6.79/7.03  thf(redefinition_r2_relset_1, axiom,
% 6.79/7.03    (![A:$i,B:$i,C:$i,D:$i]:
% 6.79/7.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.79/7.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.79/7.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.79/7.03  thf('37', plain,
% 6.79/7.03      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 6.79/7.03         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 6.79/7.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 6.79/7.03          | ((X28) = (X31))
% 6.79/7.03          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 6.79/7.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.79/7.03  thf('38', plain,
% 6.79/7.03      (![X0 : $i]:
% 6.79/7.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.79/7.03             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 6.79/7.03          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 6.79/7.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.79/7.03      inference('sup-', [status(thm)], ['36', '37'])).
% 6.79/7.03  thf('39', plain,
% 6.79/7.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 6.79/7.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.79/7.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.79/7.03            = (k6_partfun1 @ sk_A)))),
% 6.79/7.03      inference('sup-', [status(thm)], ['27', '38'])).
% 6.79/7.03  thf('40', plain,
% 6.79/7.03      (![X32 : $i]:
% 6.79/7.03         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 6.79/7.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 6.79/7.03      inference('demod', [status(thm)], ['5', '6'])).
% 6.79/7.03  thf('41', plain,
% 6.79/7.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.79/7.03         = (k6_partfun1 @ sk_A))),
% 6.79/7.03      inference('demod', [status(thm)], ['39', '40'])).
% 6.79/7.03  thf('42', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf(t26_funct_2, axiom,
% 6.79/7.03    (![A:$i,B:$i,C:$i,D:$i]:
% 6.79/7.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.79/7.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.79/7.03       ( ![E:$i]:
% 6.79/7.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 6.79/7.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.79/7.03           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 6.79/7.03             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 6.79/7.03               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 6.79/7.03  thf('43', plain,
% 6.79/7.03      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 6.79/7.03         (~ (v1_funct_1 @ X48)
% 6.79/7.03          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 6.79/7.03          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 6.79/7.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 6.79/7.03          | (v2_funct_1 @ X52)
% 6.79/7.03          | ((X50) = (k1_xboole_0))
% 6.79/7.03          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 6.79/7.03          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 6.79/7.03          | ~ (v1_funct_1 @ X52))),
% 6.79/7.03      inference('cnf', [status(esa)], [t26_funct_2])).
% 6.79/7.03  thf('44', plain,
% 6.79/7.03      (![X0 : $i, X1 : $i]:
% 6.79/7.03         (~ (v1_funct_1 @ X0)
% 6.79/7.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.79/7.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.79/7.03          | ((sk_A) = (k1_xboole_0))
% 6.79/7.03          | (v2_funct_1 @ X0)
% 6.79/7.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 6.79/7.03          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 6.79/7.03          | ~ (v1_funct_1 @ sk_D))),
% 6.79/7.03      inference('sup-', [status(thm)], ['42', '43'])).
% 6.79/7.03  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('47', plain,
% 6.79/7.03      (![X0 : $i, X1 : $i]:
% 6.79/7.03         (~ (v1_funct_1 @ X0)
% 6.79/7.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.79/7.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.79/7.03          | ((sk_A) = (k1_xboole_0))
% 6.79/7.03          | (v2_funct_1 @ X0)
% 6.79/7.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 6.79/7.03      inference('demod', [status(thm)], ['44', '45', '46'])).
% 6.79/7.03  thf('48', plain,
% 6.79/7.03      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 6.79/7.03        | (v2_funct_1 @ sk_C)
% 6.79/7.03        | ((sk_A) = (k1_xboole_0))
% 6.79/7.03        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.79/7.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 6.79/7.03        | ~ (v1_funct_1 @ sk_C))),
% 6.79/7.03      inference('sup-', [status(thm)], ['41', '47'])).
% 6.79/7.03  thf('49', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 6.79/7.03      inference('demod', [status(thm)], ['20', '21'])).
% 6.79/7.03  thf('50', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('53', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 6.79/7.03      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 6.79/7.03  thf('54', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.79/7.03      inference('split', [status(esa)], ['0'])).
% 6.79/7.03  thf('55', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.79/7.03      inference('sup-', [status(thm)], ['53', '54'])).
% 6.79/7.03  thf('56', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('57', plain,
% 6.79/7.03      (![X11 : $i, X12 : $i]:
% 6.79/7.03         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.79/7.03          | (v1_xboole_0 @ X11)
% 6.79/7.03          | ~ (v1_xboole_0 @ X12))),
% 6.79/7.03      inference('cnf', [status(esa)], [cc1_subset_1])).
% 6.79/7.03  thf('58', plain,
% 6.79/7.03      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 6.79/7.03      inference('sup-', [status(thm)], ['56', '57'])).
% 6.79/7.03  thf('59', plain,
% 6.79/7.03      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 6.79/7.03         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.79/7.03      inference('sup-', [status(thm)], ['55', '58'])).
% 6.79/7.03  thf('60', plain,
% 6.79/7.03      (![X9 : $i, X10 : $i]:
% 6.79/7.03         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 6.79/7.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.79/7.03  thf('61', plain,
% 6.79/7.03      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 6.79/7.03      inference('simplify', [status(thm)], ['60'])).
% 6.79/7.03  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.79/7.03      inference('sup-', [status(thm)], ['12', '15'])).
% 6.79/7.03  thf('63', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.79/7.03      inference('demod', [status(thm)], ['59', '61', '62'])).
% 6.79/7.03  thf('64', plain, (((v2_funct_1 @ sk_C))),
% 6.79/7.03      inference('demod', [status(thm)], ['26', '63'])).
% 6.79/7.03  thf('65', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 6.79/7.03      inference('split', [status(esa)], ['0'])).
% 6.79/7.03  thf('66', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 6.79/7.03      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 6.79/7.03  thf('67', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 6.79/7.03      inference('simpl_trail', [status(thm)], ['1', '66'])).
% 6.79/7.03  thf('68', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('69', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf(redefinition_k1_partfun1, axiom,
% 6.79/7.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.79/7.03     ( ( ( v1_funct_1 @ E ) & 
% 6.79/7.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.79/7.03         ( v1_funct_1 @ F ) & 
% 6.79/7.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.79/7.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.79/7.03  thf('70', plain,
% 6.79/7.03      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 6.79/7.03         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 6.79/7.03          | ~ (v1_funct_1 @ X41)
% 6.79/7.03          | ~ (v1_funct_1 @ X44)
% 6.79/7.03          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 6.79/7.03          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 6.79/7.03              = (k5_relat_1 @ X41 @ X44)))),
% 6.79/7.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.79/7.03  thf('71', plain,
% 6.79/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.79/7.03            = (k5_relat_1 @ sk_C @ X0))
% 6.79/7.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.79/7.03          | ~ (v1_funct_1 @ X0)
% 6.79/7.03          | ~ (v1_funct_1 @ sk_C))),
% 6.79/7.03      inference('sup-', [status(thm)], ['69', '70'])).
% 6.79/7.03  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('73', plain,
% 6.79/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.79/7.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.79/7.03            = (k5_relat_1 @ sk_C @ X0))
% 6.79/7.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.79/7.03          | ~ (v1_funct_1 @ X0))),
% 6.79/7.03      inference('demod', [status(thm)], ['71', '72'])).
% 6.79/7.03  thf('74', plain,
% 6.79/7.03      ((~ (v1_funct_1 @ sk_D)
% 6.79/7.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.79/7.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 6.79/7.03      inference('sup-', [status(thm)], ['68', '73'])).
% 6.79/7.03  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('76', plain,
% 6.79/7.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.79/7.03         = (k6_partfun1 @ sk_A))),
% 6.79/7.03      inference('demod', [status(thm)], ['39', '40'])).
% 6.79/7.03  thf('77', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 6.79/7.03      inference('demod', [status(thm)], ['74', '75', '76'])).
% 6.79/7.03  thf(t45_relat_1, axiom,
% 6.79/7.03    (![A:$i]:
% 6.79/7.03     ( ( v1_relat_1 @ A ) =>
% 6.79/7.03       ( ![B:$i]:
% 6.79/7.03         ( ( v1_relat_1 @ B ) =>
% 6.79/7.03           ( r1_tarski @
% 6.79/7.03             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 6.79/7.03  thf('78', plain,
% 6.79/7.03      (![X19 : $i, X20 : $i]:
% 6.79/7.03         (~ (v1_relat_1 @ X19)
% 6.79/7.03          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 6.79/7.03             (k2_relat_1 @ X19))
% 6.79/7.03          | ~ (v1_relat_1 @ X20))),
% 6.79/7.03      inference('cnf', [status(esa)], [t45_relat_1])).
% 6.79/7.03  thf('79', plain,
% 6.79/7.03      (![X1 : $i, X3 : $i]:
% 6.79/7.03         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 6.79/7.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.79/7.03  thf('80', plain,
% 6.79/7.03      (![X0 : $i, X1 : $i]:
% 6.79/7.03         (~ (v1_relat_1 @ X1)
% 6.79/7.03          | ~ (v1_relat_1 @ X0)
% 6.79/7.03          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 6.79/7.03               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 6.79/7.03          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 6.79/7.03      inference('sup-', [status(thm)], ['78', '79'])).
% 6.79/7.03  thf('81', plain,
% 6.79/7.03      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 6.79/7.03           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 6.79/7.03        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 6.79/7.03        | ~ (v1_relat_1 @ sk_D)
% 6.79/7.03        | ~ (v1_relat_1 @ sk_C))),
% 6.79/7.03      inference('sup-', [status(thm)], ['77', '80'])).
% 6.79/7.03  thf(t71_relat_1, axiom,
% 6.79/7.03    (![A:$i]:
% 6.79/7.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.79/7.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.79/7.03  thf('82', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 6.79/7.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.79/7.03  thf('83', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 6.79/7.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.79/7.03  thf('84', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 6.79/7.03      inference('demod', [status(thm)], ['82', '83'])).
% 6.79/7.03  thf('85', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf(cc2_relset_1, axiom,
% 6.79/7.03    (![A:$i,B:$i,C:$i]:
% 6.79/7.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.79/7.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.79/7.03  thf('86', plain,
% 6.79/7.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.79/7.03         ((v5_relat_1 @ X25 @ X27)
% 6.79/7.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.79/7.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.79/7.03  thf('87', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 6.79/7.03      inference('sup-', [status(thm)], ['85', '86'])).
% 6.79/7.03  thf(d19_relat_1, axiom,
% 6.79/7.03    (![A:$i,B:$i]:
% 6.79/7.03     ( ( v1_relat_1 @ B ) =>
% 6.79/7.03       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.79/7.03  thf('88', plain,
% 6.79/7.03      (![X15 : $i, X16 : $i]:
% 6.79/7.03         (~ (v5_relat_1 @ X15 @ X16)
% 6.79/7.03          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 6.79/7.03          | ~ (v1_relat_1 @ X15))),
% 6.79/7.03      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.79/7.03  thf('89', plain,
% 6.79/7.03      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 6.79/7.03      inference('sup-', [status(thm)], ['87', '88'])).
% 6.79/7.03  thf('90', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf(cc2_relat_1, axiom,
% 6.79/7.03    (![A:$i]:
% 6.79/7.03     ( ( v1_relat_1 @ A ) =>
% 6.79/7.03       ( ![B:$i]:
% 6.79/7.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.79/7.03  thf('91', plain,
% 6.79/7.03      (![X13 : $i, X14 : $i]:
% 6.79/7.03         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 6.79/7.03          | (v1_relat_1 @ X13)
% 6.79/7.03          | ~ (v1_relat_1 @ X14))),
% 6.79/7.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.79/7.03  thf('92', plain,
% 6.79/7.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 6.79/7.03      inference('sup-', [status(thm)], ['90', '91'])).
% 6.79/7.03  thf(fc6_relat_1, axiom,
% 6.79/7.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.79/7.03  thf('93', plain,
% 6.79/7.03      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 6.79/7.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.79/7.03  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 6.79/7.03      inference('demod', [status(thm)], ['92', '93'])).
% 6.79/7.03  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 6.79/7.03      inference('demod', [status(thm)], ['89', '94'])).
% 6.79/7.03  thf('96', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 6.79/7.03      inference('demod', [status(thm)], ['74', '75', '76'])).
% 6.79/7.03  thf('97', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 6.79/7.03      inference('demod', [status(thm)], ['82', '83'])).
% 6.79/7.03  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 6.79/7.03      inference('demod', [status(thm)], ['92', '93'])).
% 6.79/7.03  thf('99', plain,
% 6.79/7.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.79/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.79/7.03  thf('100', plain,
% 6.79/7.03      (![X13 : $i, X14 : $i]:
% 6.79/7.03         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 6.79/7.03          | (v1_relat_1 @ X13)
% 6.79/7.03          | ~ (v1_relat_1 @ X14))),
% 6.79/7.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.79/7.03  thf('101', plain,
% 6.79/7.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 6.79/7.03      inference('sup-', [status(thm)], ['99', '100'])).
% 6.79/7.03  thf('102', plain,
% 6.79/7.03      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 6.79/7.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.79/7.03  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 6.79/7.03      inference('demod', [status(thm)], ['101', '102'])).
% 6.79/7.03  thf('104', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 6.79/7.03      inference('demod', [status(thm)],
% 6.79/7.03                ['81', '84', '95', '96', '97', '98', '103'])).
% 6.79/7.03  thf('105', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 6.79/7.03      inference('simplify', [status(thm)], ['11'])).
% 6.79/7.03  thf('106', plain,
% 6.79/7.03      (![X15 : $i, X16 : $i]:
% 6.79/7.03         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 6.79/7.03          | (v5_relat_1 @ X15 @ X16)
% 6.79/7.03          | ~ (v1_relat_1 @ X15))),
% 6.79/7.03      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.79/7.03  thf('107', plain,
% 6.79/7.03      (![X0 : $i]:
% 6.79/7.03         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 6.79/7.03      inference('sup-', [status(thm)], ['105', '106'])).
% 6.79/7.03  thf(d3_funct_2, axiom,
% 6.79/7.03    (![A:$i,B:$i]:
% 6.79/7.03     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 6.79/7.03       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 6.79/7.03  thf('108', plain,
% 6.79/7.03      (![X33 : $i, X34 : $i]:
% 6.79/7.03         (((k2_relat_1 @ X34) != (X33))
% 6.79/7.03          | (v2_funct_2 @ X34 @ X33)
% 6.79/7.03          | ~ (v5_relat_1 @ X34 @ X33)
% 6.79/7.03          | ~ (v1_relat_1 @ X34))),
% 6.79/7.03      inference('cnf', [status(esa)], [d3_funct_2])).
% 6.79/7.03  thf('109', plain,
% 6.79/7.03      (![X34 : $i]:
% 6.79/7.03         (~ (v1_relat_1 @ X34)
% 6.79/7.03          | ~ (v5_relat_1 @ X34 @ (k2_relat_1 @ X34))
% 6.79/7.03          | (v2_funct_2 @ X34 @ (k2_relat_1 @ X34)))),
% 6.79/7.03      inference('simplify', [status(thm)], ['108'])).
% 6.79/7.03  thf('110', plain,
% 6.79/7.03      (![X0 : $i]:
% 6.79/7.03         (~ (v1_relat_1 @ X0)
% 6.79/7.03          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 6.79/7.03          | ~ (v1_relat_1 @ X0))),
% 6.79/7.03      inference('sup-', [status(thm)], ['107', '109'])).
% 6.79/7.03  thf('111', plain,
% 6.79/7.03      (![X0 : $i]:
% 6.79/7.03         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 6.79/7.03      inference('simplify', [status(thm)], ['110'])).
% 6.79/7.03  thf('112', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 6.79/7.03      inference('sup+', [status(thm)], ['104', '111'])).
% 6.79/7.03  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 6.79/7.03      inference('demod', [status(thm)], ['92', '93'])).
% 6.79/7.03  thf('114', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 6.79/7.03      inference('demod', [status(thm)], ['112', '113'])).
% 6.79/7.03  thf('115', plain, ($false), inference('demod', [status(thm)], ['67', '114'])).
% 6.79/7.03  
% 6.79/7.03  % SZS output end Refutation
% 6.79/7.03  
% 6.79/7.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
