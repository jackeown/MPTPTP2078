%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ctzPiyng8l

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:22 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 382 expanded)
%              Number of leaves         :   44 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          : 1317 (7547 expanded)
%              Number of equality atoms :   63 ( 116 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( ( k1_partfun1 @ X49 @ X50 @ X52 @ X53 @ X48 @ X51 )
        = ( k5_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( r2_relset_1 @ X56 @ X56 @ ( k1_partfun1 @ X56 @ X57 @ X57 @ X56 @ X55 @ X58 ) @ ( k6_partfun1 @ X56 ) )
      | ( ( k2_relset_1 @ X57 @ X56 @ X58 )
        = X56 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X56 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['17','20','23','24','25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('32',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_relat_1 @ X47 )
       != X46 )
      | ( v2_funct_2 @ X47 @ X46 )
      | ~ ( v5_relat_1 @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('33',plain,(
    ! [X47: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ~ ( v5_relat_1 @ X47 @ ( k2_relat_1 @ X47 ) )
      | ( v2_funct_2 @ X47 @ ( k2_relat_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['27','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X24 ) @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('50',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X24 ) @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('54',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('57',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('60',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41 = X44 )
      | ~ ( r2_relset_1 @ X42 @ X43 @ X41 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k4_relset_1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','66','67'])).

thf('69',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('70',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('71',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','73'])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X62 @ X60 @ X60 @ X61 @ X63 @ X59 ) )
      | ( v2_funct_1 @ X63 )
      | ( X61 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X60 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X60 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('82',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('83',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','84','85','86','87'])).

thf('89',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['88','89'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('93',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('94',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('96',plain,(
    ! [X18: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('97',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['52','90','92','95','96'])).

thf('98',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf('99',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('100',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['47','97','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ctzPiyng8l
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.88  % Solved by: fo/fo7.sh
% 0.66/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.88  % done 894 iterations in 0.432s
% 0.66/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.88  % SZS output start Refutation
% 0.66/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.88  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.66/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.66/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.66/0.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.66/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.66/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.89  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.66/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.66/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.66/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.66/0.89  thf(t29_funct_2, conjecture,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89       ( ![D:$i]:
% 0.66/0.89         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.89             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.89           ( ( r2_relset_1 @
% 0.66/0.89               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.66/0.89               ( k6_partfun1 @ A ) ) =>
% 0.66/0.89             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.66/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.89        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.89            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89          ( ![D:$i]:
% 0.66/0.89            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.89                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.89              ( ( r2_relset_1 @
% 0.66/0.89                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.66/0.89                  ( k6_partfun1 @ A ) ) =>
% 0.66/0.89                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.66/0.89    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.66/0.89  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('2', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('3', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(redefinition_k1_partfun1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.89     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.89         ( v1_funct_1 @ F ) & 
% 0.66/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.89       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.66/0.89  thf('4', plain,
% 0.66/0.89      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.66/0.89         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.66/0.89          | ~ (v1_funct_1 @ X48)
% 0.66/0.89          | ~ (v1_funct_1 @ X51)
% 0.66/0.89          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 0.66/0.89          | ((k1_partfun1 @ X49 @ X50 @ X52 @ X53 @ X48 @ X51)
% 0.66/0.89              = (k5_relat_1 @ X48 @ X51)))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.66/0.89  thf('5', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.66/0.89            = (k5_relat_1 @ sk_C @ X0))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.89          | ~ (v1_funct_1 @ X0)
% 0.66/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.89  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('7', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.66/0.89            = (k5_relat_1 @ sk_C @ X0))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.89          | ~ (v1_funct_1 @ X0))),
% 0.66/0.89      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.89  thf('8', plain,
% 0.66/0.89      ((~ (v1_funct_1 @ sk_D)
% 0.66/0.89        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['2', '7'])).
% 0.66/0.89  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('10', plain,
% 0.66/0.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.66/0.89  thf('11', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(t24_funct_2, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89       ( ![D:$i]:
% 0.66/0.89         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.66/0.89             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.66/0.89           ( ( r2_relset_1 @
% 0.66/0.89               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.66/0.89               ( k6_partfun1 @ B ) ) =>
% 0.66/0.89             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.66/0.89  thf('12', plain,
% 0.66/0.89      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.66/0.89         (~ (v1_funct_1 @ X55)
% 0.66/0.89          | ~ (v1_funct_2 @ X55 @ X56 @ X57)
% 0.66/0.89          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.66/0.89          | ~ (r2_relset_1 @ X56 @ X56 @ 
% 0.66/0.89               (k1_partfun1 @ X56 @ X57 @ X57 @ X56 @ X55 @ X58) @ 
% 0.66/0.89               (k6_partfun1 @ X56))
% 0.66/0.89          | ((k2_relset_1 @ X57 @ X56 @ X58) = (X56))
% 0.66/0.89          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56)))
% 0.66/0.89          | ~ (v1_funct_2 @ X58 @ X57 @ X56)
% 0.66/0.89          | ~ (v1_funct_1 @ X58))),
% 0.66/0.89      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.66/0.89  thf('13', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (~ (v1_funct_1 @ X0)
% 0.66/0.89          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.66/0.89          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.66/0.89          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.89               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.66/0.89               (k6_partfun1 @ sk_A))
% 0.66/0.89          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.89  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('16', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (~ (v1_funct_1 @ X0)
% 0.66/0.89          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.66/0.89          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.66/0.89          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.89               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.66/0.89               (k6_partfun1 @ sk_A)))),
% 0.66/0.89      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.66/0.89  thf('17', plain,
% 0.66/0.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.66/0.89           (k6_partfun1 @ sk_A))
% 0.66/0.89        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.66/0.89        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.66/0.89        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.66/0.89        | ~ (v1_funct_1 @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['10', '16'])).
% 0.66/0.89  thf('18', plain,
% 0.66/0.89      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.89        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.66/0.89        (k6_partfun1 @ sk_A))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('19', plain,
% 0.66/0.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.66/0.89  thf('20', plain,
% 0.66/0.89      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.66/0.89        (k6_partfun1 @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['18', '19'])).
% 0.66/0.89  thf('21', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(redefinition_k2_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.66/0.89  thf('22', plain,
% 0.66/0.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.66/0.89         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.66/0.89          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.66/0.89  thf('23', plain,
% 0.66/0.89      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.89  thf('24', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('27', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['17', '20', '23', '24', '25', '26'])).
% 0.66/0.89  thf(d10_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.89  thf('28', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.66/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.89  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.66/0.89      inference('simplify', [status(thm)], ['28'])).
% 0.66/0.89  thf(d19_relat_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( v1_relat_1 @ B ) =>
% 0.66/0.89       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.66/0.89  thf('30', plain,
% 0.66/0.89      (![X12 : $i, X13 : $i]:
% 0.66/0.89         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.66/0.89          | (v5_relat_1 @ X12 @ X13)
% 0.66/0.89          | ~ (v1_relat_1 @ X12))),
% 0.66/0.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.66/0.89  thf('31', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.89  thf(d3_funct_2, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.66/0.89       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.66/0.89  thf('32', plain,
% 0.66/0.89      (![X46 : $i, X47 : $i]:
% 0.66/0.89         (((k2_relat_1 @ X47) != (X46))
% 0.66/0.89          | (v2_funct_2 @ X47 @ X46)
% 0.66/0.89          | ~ (v5_relat_1 @ X47 @ X46)
% 0.66/0.89          | ~ (v1_relat_1 @ X47))),
% 0.66/0.89      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.66/0.89  thf('33', plain,
% 0.66/0.89      (![X47 : $i]:
% 0.66/0.89         (~ (v1_relat_1 @ X47)
% 0.66/0.89          | ~ (v5_relat_1 @ X47 @ (k2_relat_1 @ X47))
% 0.66/0.89          | (v2_funct_2 @ X47 @ (k2_relat_1 @ X47)))),
% 0.66/0.89      inference('simplify', [status(thm)], ['32'])).
% 0.66/0.89  thf('34', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (~ (v1_relat_1 @ X0)
% 0.66/0.89          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 0.66/0.89          | ~ (v1_relat_1 @ X0))),
% 0.66/0.89      inference('sup-', [status(thm)], ['31', '33'])).
% 0.66/0.89  thf('35', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.66/0.89      inference('simplify', [status(thm)], ['34'])).
% 0.66/0.89  thf('36', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 0.66/0.89      inference('sup+', [status(thm)], ['27', '35'])).
% 0.66/0.89  thf('37', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(cc2_relat_1, axiom,
% 0.66/0.89    (![A:$i]:
% 0.66/0.89     ( ( v1_relat_1 @ A ) =>
% 0.66/0.89       ( ![B:$i]:
% 0.66/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.66/0.89  thf('38', plain,
% 0.66/0.89      (![X10 : $i, X11 : $i]:
% 0.66/0.89         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.66/0.89          | (v1_relat_1 @ X10)
% 0.66/0.89          | ~ (v1_relat_1 @ X11))),
% 0.66/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.89  thf('39', plain,
% 0.66/0.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.66/0.89  thf(fc6_relat_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.66/0.89  thf('40', plain,
% 0.66/0.89      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.66/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.89  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.66/0.89      inference('demod', [status(thm)], ['39', '40'])).
% 0.66/0.89  thf('42', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.66/0.89      inference('demod', [status(thm)], ['36', '41'])).
% 0.66/0.89  thf('43', plain,
% 0.66/0.89      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('44', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.66/0.89  thf('45', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('46', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.66/0.89  thf('47', plain, (~ (v2_funct_1 @ sk_C)),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.66/0.89  thf('48', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(t162_funct_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.89       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.66/0.89  thf('49', plain,
% 0.66/0.89      (![X23 : $i, X24 : $i]:
% 0.66/0.89         (((k9_relat_1 @ (k6_relat_1 @ X24) @ X23) = (X23))
% 0.66/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.66/0.89  thf(redefinition_k6_partfun1, axiom,
% 0.66/0.89    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.66/0.89  thf('50', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.89  thf('51', plain,
% 0.66/0.89      (![X23 : $i, X24 : $i]:
% 0.66/0.89         (((k9_relat_1 @ (k6_partfun1 @ X24) @ X23) = (X23))
% 0.66/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.66/0.89      inference('demod', [status(thm)], ['49', '50'])).
% 0.66/0.89  thf('52', plain,
% 0.66/0.89      (((k9_relat_1 @ (k6_partfun1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_C)
% 0.66/0.89         = (sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['48', '51'])).
% 0.66/0.89  thf('53', plain,
% 0.66/0.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.66/0.89  thf('54', plain,
% 0.66/0.89      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.66/0.89        (k6_partfun1 @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['18', '19'])).
% 0.66/0.89  thf('55', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('56', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(dt_k4_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.89     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.89       ( m1_subset_1 @
% 0.66/0.89         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.66/0.89         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.66/0.89  thf('57', plain,
% 0.66/0.89      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.89         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.66/0.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.66/0.89          | (m1_subset_1 @ (k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.66/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.66/0.89      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.66/0.89  thf('58', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.66/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.66/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.66/0.89  thf('59', plain,
% 0.66/0.89      ((m1_subset_1 @ 
% 0.66/0.89        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.66/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['55', '58'])).
% 0.66/0.89  thf(redefinition_r2_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.89     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.66/0.89  thf('60', plain,
% 0.66/0.89      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.66/0.89         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.66/0.89          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.66/0.89          | ((X41) = (X44))
% 0.66/0.89          | ~ (r2_relset_1 @ X42 @ X43 @ X41 @ X44))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.66/0.89  thf('61', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.89             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.66/0.89          | ((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['59', '60'])).
% 0.66/0.89  thf('62', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('63', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(redefinition_k4_relset_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.89     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.89       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.66/0.89  thf('64', plain,
% 0.66/0.89      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.66/0.89         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.66/0.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.66/0.89          | ((k4_relset_1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.66/0.89              = (k5_relat_1 @ X35 @ X38)))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.66/0.89  thf('65', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.66/0.89            = (k5_relat_1 @ sk_C @ X0))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['63', '64'])).
% 0.66/0.89  thf('66', plain,
% 0.66/0.89      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['62', '65'])).
% 0.66/0.89  thf('67', plain,
% 0.66/0.89      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['62', '65'])).
% 0.66/0.89  thf('68', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.66/0.89          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.66/0.89      inference('demod', [status(thm)], ['61', '66', '67'])).
% 0.66/0.89  thf('69', plain,
% 0.66/0.89      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.66/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.66/0.89        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['54', '68'])).
% 0.66/0.89  thf(t29_relset_1, axiom,
% 0.66/0.89    (![A:$i]:
% 0.66/0.89     ( m1_subset_1 @
% 0.66/0.89       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.66/0.89  thf('70', plain,
% 0.66/0.89      (![X45 : $i]:
% 0.66/0.89         (m1_subset_1 @ (k6_relat_1 @ X45) @ 
% 0.66/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.66/0.89  thf('71', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.89  thf('72', plain,
% 0.66/0.89      (![X45 : $i]:
% 0.66/0.89         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 0.66/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 0.66/0.89      inference('demod', [status(thm)], ['70', '71'])).
% 0.66/0.89  thf('73', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['69', '72'])).
% 0.66/0.89  thf('74', plain,
% 0.66/0.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.66/0.89         = (k6_partfun1 @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['53', '73'])).
% 0.66/0.89  thf('75', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf(t26_funct_2, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.66/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.89       ( ![E:$i]:
% 0.66/0.89         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.66/0.89             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.66/0.89           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.66/0.89             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.66/0.89               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.66/0.89  thf('76', plain,
% 0.66/0.89      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.66/0.89         (~ (v1_funct_1 @ X59)
% 0.66/0.89          | ~ (v1_funct_2 @ X59 @ X60 @ X61)
% 0.66/0.89          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.66/0.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X62 @ X60 @ X60 @ X61 @ X63 @ X59))
% 0.66/0.89          | (v2_funct_1 @ X63)
% 0.66/0.89          | ((X61) = (k1_xboole_0))
% 0.66/0.89          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X60)))
% 0.66/0.89          | ~ (v1_funct_2 @ X63 @ X62 @ X60)
% 0.66/0.89          | ~ (v1_funct_1 @ X63))),
% 0.66/0.89      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.66/0.89  thf('77', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         (~ (v1_funct_1 @ X0)
% 0.66/0.89          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.66/0.89          | ((sk_A) = (k1_xboole_0))
% 0.66/0.89          | (v2_funct_1 @ X0)
% 0.66/0.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.66/0.89          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.66/0.89          | ~ (v1_funct_1 @ sk_D))),
% 0.66/0.89      inference('sup-', [status(thm)], ['75', '76'])).
% 0.66/0.89  thf('78', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('80', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         (~ (v1_funct_1 @ X0)
% 0.66/0.89          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.66/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.66/0.89          | ((sk_A) = (k1_xboole_0))
% 0.66/0.89          | (v2_funct_1 @ X0)
% 0.66/0.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.66/0.89      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.66/0.89  thf('81', plain,
% 0.66/0.89      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.66/0.89        | (v2_funct_1 @ sk_C)
% 0.66/0.89        | ((sk_A) = (k1_xboole_0))
% 0.66/0.89        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.66/0.89        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.66/0.89        | ~ (v1_funct_1 @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['74', '80'])).
% 0.66/0.89  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.66/0.89  thf('82', plain, (![X25 : $i]: (v2_funct_1 @ (k6_relat_1 @ X25))),
% 0.66/0.89      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.66/0.89  thf('83', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.89  thf('84', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 0.66/0.89      inference('demod', [status(thm)], ['82', '83'])).
% 0.66/0.89  thf('85', plain,
% 0.66/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('86', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('88', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.66/0.89      inference('demod', [status(thm)], ['81', '84', '85', '86', '87'])).
% 0.66/0.89  thf('89', plain, (~ (v2_funct_1 @ sk_C)),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.66/0.89  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.66/0.89      inference('clc', [status(thm)], ['88', '89'])).
% 0.66/0.89  thf(t113_zfmisc_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.66/0.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.66/0.89  thf('91', plain,
% 0.66/0.89      (![X4 : $i, X5 : $i]:
% 0.66/0.89         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.66/0.89  thf('92', plain,
% 0.66/0.89      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.66/0.89      inference('simplify', [status(thm)], ['91'])).
% 0.66/0.89  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.66/0.89  thf('93', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.89      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.66/0.89  thf('94', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.66/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.89  thf('95', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.89      inference('demod', [status(thm)], ['93', '94'])).
% 0.66/0.89  thf(t150_relat_1, axiom,
% 0.66/0.89    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.66/0.89  thf('96', plain,
% 0.66/0.89      (![X18 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.66/0.89      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.66/0.89  thf('97', plain, (((k1_xboole_0) = (sk_C))),
% 0.66/0.89      inference('demod', [status(thm)], ['52', '90', '92', '95', '96'])).
% 0.66/0.89  thf('98', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.89      inference('demod', [status(thm)], ['93', '94'])).
% 0.66/0.89  thf('99', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 0.66/0.89      inference('demod', [status(thm)], ['82', '83'])).
% 0.66/0.89  thf('100', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.66/0.89      inference('sup+', [status(thm)], ['98', '99'])).
% 0.66/0.89  thf('101', plain, ($false),
% 0.66/0.89      inference('demod', [status(thm)], ['47', '97', '100'])).
% 0.66/0.89  
% 0.66/0.89  % SZS output end Refutation
% 0.66/0.89  
% 0.66/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
