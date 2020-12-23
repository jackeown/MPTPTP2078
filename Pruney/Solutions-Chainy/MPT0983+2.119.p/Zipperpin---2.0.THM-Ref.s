%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TqDp8ygAuX

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:20 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 333 expanded)
%              Number of leaves         :   47 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          : 1234 (5330 expanded)
%              Number of equality atoms :   49 (  85 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

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
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
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
    | ( v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
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
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('21',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
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
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    inference(demod,[status(thm)],['24','63'])).

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
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('77',plain,
    ( ( k6_relat_1 @ sk_A )
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
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('89',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('95',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','93','94','95','96','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('104',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('106',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('107',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('112',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['67','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TqDp8ygAuX
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:57:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 3.86/4.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.86/4.07  % Solved by: fo/fo7.sh
% 3.86/4.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.86/4.07  % done 4868 iterations in 3.603s
% 3.86/4.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.86/4.07  % SZS output start Refutation
% 3.86/4.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.86/4.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.86/4.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.86/4.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.86/4.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.86/4.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.86/4.07  thf(sk_C_type, type, sk_C: $i).
% 3.86/4.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.86/4.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.86/4.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.86/4.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.86/4.07  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.86/4.07  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.86/4.07  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.86/4.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.86/4.07  thf(sk_D_type, type, sk_D: $i).
% 3.86/4.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.86/4.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.86/4.07  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.86/4.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.86/4.07  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.86/4.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.86/4.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.86/4.07  thf(sk_B_type, type, sk_B: $i).
% 3.86/4.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.86/4.07  thf(sk_A_type, type, sk_A: $i).
% 3.86/4.07  thf(t29_funct_2, conjecture,
% 3.86/4.07    (![A:$i,B:$i,C:$i]:
% 3.86/4.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.86/4.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.86/4.07       ( ![D:$i]:
% 3.86/4.07         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.86/4.07             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.86/4.07           ( ( r2_relset_1 @
% 3.86/4.07               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.86/4.07               ( k6_partfun1 @ A ) ) =>
% 3.86/4.07             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.86/4.07  thf(zf_stmt_0, negated_conjecture,
% 3.86/4.07    (~( ![A:$i,B:$i,C:$i]:
% 3.86/4.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.86/4.07            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.86/4.07          ( ![D:$i]:
% 3.86/4.07            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.86/4.07                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.86/4.07              ( ( r2_relset_1 @
% 3.86/4.07                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.86/4.07                  ( k6_partfun1 @ A ) ) =>
% 3.86/4.07                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.86/4.07    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.86/4.07  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('1', plain,
% 3.86/4.07      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.86/4.07      inference('split', [status(esa)], ['0'])).
% 3.86/4.07  thf(l13_xboole_0, axiom,
% 3.86/4.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.86/4.07  thf('2', plain,
% 3.86/4.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.86/4.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.86/4.07  thf(t113_zfmisc_1, axiom,
% 3.86/4.07    (![A:$i,B:$i]:
% 3.86/4.07     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.86/4.07       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.86/4.07  thf('3', plain,
% 3.86/4.07      (![X9 : $i, X10 : $i]:
% 3.86/4.07         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 3.86/4.07      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.86/4.07  thf('4', plain,
% 3.86/4.07      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 3.86/4.07      inference('simplify', [status(thm)], ['3'])).
% 3.86/4.07  thf(dt_k6_partfun1, axiom,
% 3.86/4.07    (![A:$i]:
% 3.86/4.07     ( ( m1_subset_1 @
% 3.86/4.07         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.86/4.07       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.86/4.07  thf('5', plain,
% 3.86/4.07      (![X40 : $i]:
% 3.86/4.07         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 3.86/4.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.86/4.07      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.86/4.07  thf(redefinition_k6_partfun1, axiom,
% 3.86/4.07    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.86/4.07  thf('6', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.86/4.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.86/4.07  thf('7', plain,
% 3.86/4.07      (![X40 : $i]:
% 3.86/4.07         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 3.86/4.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.86/4.07      inference('demod', [status(thm)], ['5', '6'])).
% 3.86/4.07  thf('8', plain,
% 3.86/4.07      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.86/4.07      inference('sup+', [status(thm)], ['4', '7'])).
% 3.86/4.07  thf(cc1_subset_1, axiom,
% 3.86/4.07    (![A:$i]:
% 3.86/4.07     ( ( v1_xboole_0 @ A ) =>
% 3.86/4.07       ( ![B:$i]:
% 3.86/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.86/4.07  thf('9', plain,
% 3.86/4.07      (![X11 : $i, X12 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 3.86/4.07          | (v1_xboole_0 @ X11)
% 3.86/4.07          | ~ (v1_xboole_0 @ X12))),
% 3.86/4.07      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.86/4.07  thf('10', plain,
% 3.86/4.07      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.86/4.07        | (v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['8', '9'])).
% 3.86/4.07  thf(d10_xboole_0, axiom,
% 3.86/4.07    (![A:$i,B:$i]:
% 3.86/4.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.86/4.07  thf('11', plain,
% 3.86/4.07      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 3.86/4.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.86/4.07  thf('12', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.86/4.07      inference('simplify', [status(thm)], ['11'])).
% 3.86/4.07  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 3.86/4.07  thf('13', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 3.86/4.07      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.86/4.07  thf(t69_xboole_1, axiom,
% 3.86/4.07    (![A:$i,B:$i]:
% 3.86/4.07     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.86/4.07       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 3.86/4.07  thf('14', plain,
% 3.86/4.07      (![X6 : $i, X7 : $i]:
% 3.86/4.07         (~ (r1_xboole_0 @ X6 @ X7)
% 3.86/4.07          | ~ (r1_tarski @ X6 @ X7)
% 3.86/4.07          | (v1_xboole_0 @ X6))),
% 3.86/4.07      inference('cnf', [status(esa)], [t69_xboole_1])).
% 3.86/4.07  thf('15', plain,
% 3.86/4.07      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.86/4.07      inference('sup-', [status(thm)], ['13', '14'])).
% 3.86/4.07  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.86/4.07      inference('sup-', [status(thm)], ['12', '15'])).
% 3.86/4.07  thf('17', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.86/4.07      inference('demod', [status(thm)], ['10', '16'])).
% 3.86/4.07  thf('18', plain,
% 3.86/4.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.86/4.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.86/4.07  thf('19', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.86/4.07      inference('sup-', [status(thm)], ['17', '18'])).
% 3.86/4.07  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.86/4.07  thf('20', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 3.86/4.07      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.86/4.07  thf('21', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.86/4.07      inference('sup+', [status(thm)], ['19', '20'])).
% 3.86/4.07  thf('22', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.86/4.07      inference('sup+', [status(thm)], ['2', '21'])).
% 3.86/4.07  thf('23', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.86/4.07      inference('split', [status(esa)], ['0'])).
% 3.86/4.07  thf('24', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['22', '23'])).
% 3.86/4.07  thf('25', plain,
% 3.86/4.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.86/4.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.86/4.07        (k6_partfun1 @ sk_A))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('26', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.86/4.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.86/4.07  thf('27', plain,
% 3.86/4.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.86/4.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.86/4.07        (k6_relat_1 @ sk_A))),
% 3.86/4.07      inference('demod', [status(thm)], ['25', '26'])).
% 3.86/4.07  thf('28', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('29', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf(dt_k1_partfun1, axiom,
% 3.86/4.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.86/4.07     ( ( ( v1_funct_1 @ E ) & 
% 3.86/4.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.86/4.07         ( v1_funct_1 @ F ) & 
% 3.86/4.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.86/4.07       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.86/4.07         ( m1_subset_1 @
% 3.86/4.07           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.86/4.07           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.86/4.07  thf('30', plain,
% 3.86/4.07      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.86/4.07          | ~ (v1_funct_1 @ X33)
% 3.86/4.07          | ~ (v1_funct_1 @ X36)
% 3.86/4.07          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.86/4.07          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 3.86/4.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 3.86/4.07      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.86/4.07  thf('31', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.86/4.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.86/4.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.86/4.07          | ~ (v1_funct_1 @ X1)
% 3.86/4.07          | ~ (v1_funct_1 @ sk_C))),
% 3.86/4.07      inference('sup-', [status(thm)], ['29', '30'])).
% 3.86/4.07  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('33', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.86/4.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.86/4.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.86/4.07          | ~ (v1_funct_1 @ X1))),
% 3.86/4.07      inference('demod', [status(thm)], ['31', '32'])).
% 3.86/4.07  thf('34', plain,
% 3.86/4.07      ((~ (v1_funct_1 @ sk_D)
% 3.86/4.07        | (m1_subset_1 @ 
% 3.86/4.07           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.86/4.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.86/4.07      inference('sup-', [status(thm)], ['28', '33'])).
% 3.86/4.07  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('36', plain,
% 3.86/4.07      ((m1_subset_1 @ 
% 3.86/4.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.86/4.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.86/4.07      inference('demod', [status(thm)], ['34', '35'])).
% 3.86/4.07  thf(redefinition_r2_relset_1, axiom,
% 3.86/4.07    (![A:$i,B:$i,C:$i,D:$i]:
% 3.86/4.07     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.86/4.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.86/4.07       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.86/4.07  thf('37', plain,
% 3.86/4.07      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.86/4.07          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.86/4.07          | ((X27) = (X30))
% 3.86/4.07          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 3.86/4.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.86/4.07  thf('38', plain,
% 3.86/4.07      (![X0 : $i]:
% 3.86/4.07         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.86/4.07             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.86/4.07          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.86/4.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.86/4.07      inference('sup-', [status(thm)], ['36', '37'])).
% 3.86/4.07  thf('39', plain,
% 3.86/4.07      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.86/4.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.86/4.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.86/4.07            = (k6_relat_1 @ sk_A)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['27', '38'])).
% 3.86/4.07  thf('40', plain,
% 3.86/4.07      (![X40 : $i]:
% 3.86/4.07         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 3.86/4.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 3.86/4.07      inference('demod', [status(thm)], ['5', '6'])).
% 3.86/4.07  thf('41', plain,
% 3.86/4.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.86/4.07         = (k6_relat_1 @ sk_A))),
% 3.86/4.07      inference('demod', [status(thm)], ['39', '40'])).
% 3.86/4.07  thf('42', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf(t26_funct_2, axiom,
% 3.86/4.07    (![A:$i,B:$i,C:$i,D:$i]:
% 3.86/4.07     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.86/4.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.86/4.07       ( ![E:$i]:
% 3.86/4.07         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.86/4.07             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.86/4.07           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.86/4.07             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.86/4.07               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.86/4.07  thf('43', plain,
% 3.86/4.07      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.86/4.07         (~ (v1_funct_1 @ X48)
% 3.86/4.07          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 3.86/4.07          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 3.86/4.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 3.86/4.07          | (v2_funct_1 @ X52)
% 3.86/4.07          | ((X50) = (k1_xboole_0))
% 3.86/4.07          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 3.86/4.07          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 3.86/4.07          | ~ (v1_funct_1 @ X52))),
% 3.86/4.07      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.86/4.07  thf('44', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i]:
% 3.86/4.07         (~ (v1_funct_1 @ X0)
% 3.86/4.07          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.86/4.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.86/4.07          | ((sk_A) = (k1_xboole_0))
% 3.86/4.07          | (v2_funct_1 @ X0)
% 3.86/4.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.86/4.07          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.86/4.07          | ~ (v1_funct_1 @ sk_D))),
% 3.86/4.07      inference('sup-', [status(thm)], ['42', '43'])).
% 3.86/4.07  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('47', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i]:
% 3.86/4.07         (~ (v1_funct_1 @ X0)
% 3.86/4.07          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.86/4.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.86/4.07          | ((sk_A) = (k1_xboole_0))
% 3.86/4.07          | (v2_funct_1 @ X0)
% 3.86/4.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.86/4.07      inference('demod', [status(thm)], ['44', '45', '46'])).
% 3.86/4.07  thf('48', plain,
% 3.86/4.07      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.86/4.07        | (v2_funct_1 @ sk_C)
% 3.86/4.07        | ((sk_A) = (k1_xboole_0))
% 3.86/4.07        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.86/4.07        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.86/4.07        | ~ (v1_funct_1 @ sk_C))),
% 3.86/4.07      inference('sup-', [status(thm)], ['41', '47'])).
% 3.86/4.07  thf('49', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 3.86/4.07      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.86/4.07  thf('50', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('53', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.86/4.07      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 3.86/4.07  thf('54', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.86/4.07      inference('split', [status(esa)], ['0'])).
% 3.86/4.07  thf('55', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['53', '54'])).
% 3.86/4.07  thf('56', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('57', plain,
% 3.86/4.07      (![X11 : $i, X12 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 3.86/4.07          | (v1_xboole_0 @ X11)
% 3.86/4.07          | ~ (v1_xboole_0 @ X12))),
% 3.86/4.07      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.86/4.07  thf('58', plain,
% 3.86/4.07      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.86/4.07      inference('sup-', [status(thm)], ['56', '57'])).
% 3.86/4.07  thf('59', plain,
% 3.86/4.07      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 3.86/4.07         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['55', '58'])).
% 3.86/4.07  thf('60', plain,
% 3.86/4.07      (![X9 : $i, X10 : $i]:
% 3.86/4.07         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 3.86/4.07      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.86/4.07  thf('61', plain,
% 3.86/4.07      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 3.86/4.07      inference('simplify', [status(thm)], ['60'])).
% 3.86/4.07  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.86/4.07      inference('sup-', [status(thm)], ['12', '15'])).
% 3.86/4.07  thf('63', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.86/4.07      inference('demod', [status(thm)], ['59', '61', '62'])).
% 3.86/4.07  thf('64', plain, (((v2_funct_1 @ sk_C))),
% 3.86/4.07      inference('demod', [status(thm)], ['24', '63'])).
% 3.86/4.07  thf('65', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.86/4.07      inference('split', [status(esa)], ['0'])).
% 3.86/4.07  thf('66', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.86/4.07      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 3.86/4.07  thf('67', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.86/4.07      inference('simpl_trail', [status(thm)], ['1', '66'])).
% 3.86/4.07  thf('68', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('69', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf(redefinition_k1_partfun1, axiom,
% 3.86/4.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.86/4.07     ( ( ( v1_funct_1 @ E ) & 
% 3.86/4.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.86/4.07         ( v1_funct_1 @ F ) & 
% 3.86/4.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.86/4.07       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.86/4.07  thf('70', plain,
% 3.86/4.07      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.86/4.07          | ~ (v1_funct_1 @ X41)
% 3.86/4.07          | ~ (v1_funct_1 @ X44)
% 3.86/4.07          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.86/4.07          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 3.86/4.07              = (k5_relat_1 @ X41 @ X44)))),
% 3.86/4.07      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.86/4.07  thf('71', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.86/4.07            = (k5_relat_1 @ sk_C @ X0))
% 3.86/4.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.86/4.07          | ~ (v1_funct_1 @ X0)
% 3.86/4.07          | ~ (v1_funct_1 @ sk_C))),
% 3.86/4.07      inference('sup-', [status(thm)], ['69', '70'])).
% 3.86/4.07  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('73', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.86/4.07            = (k5_relat_1 @ sk_C @ X0))
% 3.86/4.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.86/4.07          | ~ (v1_funct_1 @ X0))),
% 3.86/4.07      inference('demod', [status(thm)], ['71', '72'])).
% 3.86/4.07  thf('74', plain,
% 3.86/4.07      ((~ (v1_funct_1 @ sk_D)
% 3.86/4.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.86/4.07            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['68', '73'])).
% 3.86/4.07  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('76', plain,
% 3.86/4.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.86/4.07         = (k6_relat_1 @ sk_A))),
% 3.86/4.07      inference('demod', [status(thm)], ['39', '40'])).
% 3.86/4.07  thf('77', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.86/4.07      inference('demod', [status(thm)], ['74', '75', '76'])).
% 3.86/4.07  thf(t45_relat_1, axiom,
% 3.86/4.07    (![A:$i]:
% 3.86/4.07     ( ( v1_relat_1 @ A ) =>
% 3.86/4.07       ( ![B:$i]:
% 3.86/4.07         ( ( v1_relat_1 @ B ) =>
% 3.86/4.07           ( r1_tarski @
% 3.86/4.07             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.86/4.07  thf('78', plain,
% 3.86/4.07      (![X19 : $i, X20 : $i]:
% 3.86/4.07         (~ (v1_relat_1 @ X19)
% 3.86/4.07          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 3.86/4.07             (k2_relat_1 @ X19))
% 3.86/4.07          | ~ (v1_relat_1 @ X20))),
% 3.86/4.07      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.86/4.07  thf('79', plain,
% 3.86/4.07      (![X1 : $i, X3 : $i]:
% 3.86/4.07         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 3.86/4.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.86/4.07  thf('80', plain,
% 3.86/4.07      (![X0 : $i, X1 : $i]:
% 3.86/4.07         (~ (v1_relat_1 @ X1)
% 3.86/4.07          | ~ (v1_relat_1 @ X0)
% 3.86/4.07          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.86/4.07               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.86/4.07          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.86/4.07      inference('sup-', [status(thm)], ['78', '79'])).
% 3.86/4.07  thf('81', plain,
% 3.86/4.07      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k2_relat_1 @ (k6_relat_1 @ sk_A)))
% 3.86/4.07        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.86/4.07        | ~ (v1_relat_1 @ sk_D)
% 3.86/4.07        | ~ (v1_relat_1 @ sk_C))),
% 3.86/4.07      inference('sup-', [status(thm)], ['77', '80'])).
% 3.86/4.07  thf(t71_relat_1, axiom,
% 3.86/4.07    (![A:$i]:
% 3.86/4.07     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.86/4.07       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.86/4.07  thf('82', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 3.86/4.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.86/4.07  thf('83', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf(cc2_relset_1, axiom,
% 3.86/4.07    (![A:$i,B:$i,C:$i]:
% 3.86/4.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.86/4.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.86/4.07  thf('84', plain,
% 3.86/4.07      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.86/4.07         ((v5_relat_1 @ X24 @ X26)
% 3.86/4.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.86/4.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.86/4.07  thf('85', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.86/4.07      inference('sup-', [status(thm)], ['83', '84'])).
% 3.86/4.07  thf(d19_relat_1, axiom,
% 3.86/4.07    (![A:$i,B:$i]:
% 3.86/4.07     ( ( v1_relat_1 @ B ) =>
% 3.86/4.07       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.86/4.07  thf('86', plain,
% 3.86/4.07      (![X15 : $i, X16 : $i]:
% 3.86/4.07         (~ (v5_relat_1 @ X15 @ X16)
% 3.86/4.07          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 3.86/4.07          | ~ (v1_relat_1 @ X15))),
% 3.86/4.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.86/4.07  thf('87', plain,
% 3.86/4.07      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.86/4.07      inference('sup-', [status(thm)], ['85', '86'])).
% 3.86/4.07  thf('88', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf(cc2_relat_1, axiom,
% 3.86/4.07    (![A:$i]:
% 3.86/4.07     ( ( v1_relat_1 @ A ) =>
% 3.86/4.07       ( ![B:$i]:
% 3.86/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.86/4.07  thf('89', plain,
% 3.86/4.07      (![X13 : $i, X14 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 3.86/4.07          | (v1_relat_1 @ X13)
% 3.86/4.07          | ~ (v1_relat_1 @ X14))),
% 3.86/4.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.86/4.07  thf('90', plain,
% 3.86/4.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.86/4.07      inference('sup-', [status(thm)], ['88', '89'])).
% 3.86/4.07  thf(fc6_relat_1, axiom,
% 3.86/4.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.86/4.07  thf('91', plain,
% 3.86/4.07      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 3.86/4.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.86/4.07  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 3.86/4.07      inference('demod', [status(thm)], ['90', '91'])).
% 3.86/4.07  thf('93', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.86/4.07      inference('demod', [status(thm)], ['87', '92'])).
% 3.86/4.07  thf('94', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.86/4.07      inference('demod', [status(thm)], ['74', '75', '76'])).
% 3.86/4.07  thf('95', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 3.86/4.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.86/4.07  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 3.86/4.07      inference('demod', [status(thm)], ['90', '91'])).
% 3.86/4.07  thf('97', plain,
% 3.86/4.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.86/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.07  thf('98', plain,
% 3.86/4.07      (![X13 : $i, X14 : $i]:
% 3.86/4.07         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 3.86/4.07          | (v1_relat_1 @ X13)
% 3.86/4.07          | ~ (v1_relat_1 @ X14))),
% 3.86/4.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.86/4.07  thf('99', plain,
% 3.86/4.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.86/4.07      inference('sup-', [status(thm)], ['97', '98'])).
% 3.86/4.07  thf('100', plain,
% 3.86/4.07      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 3.86/4.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.86/4.07  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 3.86/4.07      inference('demod', [status(thm)], ['99', '100'])).
% 3.86/4.07  thf('102', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.86/4.07      inference('demod', [status(thm)],
% 3.86/4.07                ['81', '82', '93', '94', '95', '96', '101'])).
% 3.86/4.07  thf('103', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.86/4.07      inference('simplify', [status(thm)], ['11'])).
% 3.86/4.07  thf('104', plain,
% 3.86/4.07      (![X15 : $i, X16 : $i]:
% 3.86/4.07         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 3.86/4.07          | (v5_relat_1 @ X15 @ X16)
% 3.86/4.07          | ~ (v1_relat_1 @ X15))),
% 3.86/4.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.86/4.07  thf('105', plain,
% 3.86/4.07      (![X0 : $i]:
% 3.86/4.07         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.86/4.07      inference('sup-', [status(thm)], ['103', '104'])).
% 3.86/4.07  thf(d3_funct_2, axiom,
% 3.86/4.07    (![A:$i,B:$i]:
% 3.86/4.07     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.86/4.07       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.86/4.07  thf('106', plain,
% 3.86/4.07      (![X31 : $i, X32 : $i]:
% 3.86/4.07         (((k2_relat_1 @ X32) != (X31))
% 3.86/4.07          | (v2_funct_2 @ X32 @ X31)
% 3.86/4.07          | ~ (v5_relat_1 @ X32 @ X31)
% 3.86/4.07          | ~ (v1_relat_1 @ X32))),
% 3.86/4.07      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.86/4.07  thf('107', plain,
% 3.86/4.07      (![X32 : $i]:
% 3.86/4.07         (~ (v1_relat_1 @ X32)
% 3.86/4.07          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 3.86/4.07          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 3.86/4.07      inference('simplify', [status(thm)], ['106'])).
% 3.86/4.07  thf('108', plain,
% 3.86/4.07      (![X0 : $i]:
% 3.86/4.07         (~ (v1_relat_1 @ X0)
% 3.86/4.07          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.86/4.07          | ~ (v1_relat_1 @ X0))),
% 3.86/4.07      inference('sup-', [status(thm)], ['105', '107'])).
% 3.86/4.07  thf('109', plain,
% 3.86/4.07      (![X0 : $i]:
% 3.86/4.07         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.86/4.07      inference('simplify', [status(thm)], ['108'])).
% 3.86/4.07  thf('110', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.86/4.07      inference('sup+', [status(thm)], ['102', '109'])).
% 3.86/4.07  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 3.86/4.07      inference('demod', [status(thm)], ['90', '91'])).
% 3.86/4.07  thf('112', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.86/4.07      inference('demod', [status(thm)], ['110', '111'])).
% 3.86/4.07  thf('113', plain, ($false), inference('demod', [status(thm)], ['67', '112'])).
% 3.86/4.07  
% 3.86/4.07  % SZS output end Refutation
% 3.86/4.07  
% 3.92/4.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
