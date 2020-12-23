%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.emfNClaLXA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:17 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 596 expanded)
%              Number of leaves         :   37 ( 197 expanded)
%              Depth                    :   18
%              Number of atoms          : 1714 (12778 expanded)
%              Number of equality atoms :   61 ( 144 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('34',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('38',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('53',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('60',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('66',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','63','64','65'])).

thf('67',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('68',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( X10 = X13 )
      | ~ ( r2_relset_1 @ X11 @ X12 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('76',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('78',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( r2_relset_1 @ X11 @ X12 @ X10 @ X13 )
      | ( X10 != X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['76','80'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','81'])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('93',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('102',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('103',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('105',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('110',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('111',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['106','107','108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('114',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['106','107','108','111'])).

thf('120',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('123',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('125',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['106','107','108','111'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('128',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['106','107','108','111'])).

thf('132',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['106','107','108','111'])).

thf('133',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('134',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('136',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135'])).

thf('137',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','136'])).

thf('138',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['100','103','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['91','138','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.emfNClaLXA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.23/1.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.23/1.46  % Solved by: fo/fo7.sh
% 1.23/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.23/1.46  % done 1228 iterations in 0.999s
% 1.23/1.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.23/1.46  % SZS output start Refutation
% 1.23/1.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.23/1.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.23/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.23/1.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.23/1.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.23/1.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.23/1.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.23/1.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.23/1.46  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.23/1.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.23/1.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.23/1.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.23/1.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.23/1.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.23/1.46  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.23/1.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.23/1.46  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.23/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.23/1.46  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.23/1.46  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.23/1.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.23/1.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.23/1.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.23/1.46  thf(t88_funct_2, conjecture,
% 1.23/1.46    (![A:$i,B:$i]:
% 1.23/1.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( v3_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.23/1.46       ( ( r2_relset_1 @
% 1.23/1.46           A @ A @ 
% 1.23/1.46           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.23/1.46           ( k6_partfun1 @ A ) ) & 
% 1.23/1.46         ( r2_relset_1 @
% 1.23/1.46           A @ A @ 
% 1.23/1.46           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.23/1.46           ( k6_partfun1 @ A ) ) ) ))).
% 1.23/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.23/1.46    (~( ![A:$i,B:$i]:
% 1.23/1.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.23/1.46            ( v3_funct_2 @ B @ A @ A ) & 
% 1.23/1.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.23/1.46          ( ( r2_relset_1 @
% 1.23/1.46              A @ A @ 
% 1.23/1.46              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.23/1.46              ( k6_partfun1 @ A ) ) & 
% 1.23/1.46            ( r2_relset_1 @
% 1.23/1.46              A @ A @ 
% 1.23/1.46              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.23/1.46              ( k6_partfun1 @ A ) ) ) ) )),
% 1.23/1.46    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.23/1.46  thf('0', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A))
% 1.23/1.46        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46             (k6_partfun1 @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('1', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A)))
% 1.23/1.46         <= (~
% 1.23/1.46             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.23/1.46               (k6_partfun1 @ sk_A))))),
% 1.23/1.46      inference('split', [status(esa)], ['0'])).
% 1.23/1.46  thf('2', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(redefinition_k2_funct_2, axiom,
% 1.23/1.46    (![A:$i,B:$i]:
% 1.23/1.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( v3_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.23/1.46       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.23/1.46  thf('3', plain,
% 1.23/1.46      (![X28 : $i, X29 : $i]:
% 1.23/1.46         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 1.23/1.46          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 1.23/1.46          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 1.23/1.46          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 1.23/1.46          | ~ (v1_funct_1 @ X28))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.23/1.46  thf('4', plain,
% 1.23/1.46      ((~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['2', '3'])).
% 1.23/1.46  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.23/1.46  thf('9', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46            (k2_funct_1 @ sk_B)) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A)))
% 1.23/1.46         <= (~
% 1.23/1.46             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.23/1.46               (k6_partfun1 @ sk_A))))),
% 1.23/1.46      inference('demod', [status(thm)], ['1', '8'])).
% 1.23/1.46  thf('10', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('11', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(dt_k2_funct_2, axiom,
% 1.23/1.46    (![A:$i,B:$i]:
% 1.23/1.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( v3_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.23/1.46       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.23/1.46         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.23/1.46         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.23/1.46         ( m1_subset_1 @
% 1.23/1.46           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.23/1.46  thf('12', plain,
% 1.23/1.46      (![X20 : $i, X21 : $i]:
% 1.23/1.46         ((m1_subset_1 @ (k2_funct_2 @ X20 @ X21) @ 
% 1.23/1.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 1.23/1.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 1.23/1.46          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 1.23/1.46          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 1.23/1.46          | ~ (v1_funct_1 @ X21))),
% 1.23/1.46      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.23/1.46  thf('13', plain,
% 1.23/1.46      ((~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.23/1.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['11', '12'])).
% 1.23/1.46  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('17', plain,
% 1.23/1.46      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.23/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 1.23/1.46  thf(redefinition_k1_partfun1, axiom,
% 1.23/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.23/1.46     ( ( ( v1_funct_1 @ E ) & 
% 1.23/1.46         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.23/1.46         ( v1_funct_1 @ F ) & 
% 1.23/1.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.23/1.46       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.23/1.46  thf('18', plain,
% 1.23/1.46      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.23/1.46         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.23/1.46          | ~ (v1_funct_1 @ X22)
% 1.23/1.46          | ~ (v1_funct_1 @ X25)
% 1.23/1.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.23/1.46          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 1.23/1.46              = (k5_relat_1 @ X22 @ X25)))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.23/1.46  thf('19', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.23/1.46         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.23/1.46            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 1.23/1.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['17', '18'])).
% 1.23/1.46  thf('20', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('21', plain,
% 1.23/1.46      (![X20 : $i, X21 : $i]:
% 1.23/1.46         ((v1_funct_1 @ (k2_funct_2 @ X20 @ X21))
% 1.23/1.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 1.23/1.46          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 1.23/1.46          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 1.23/1.46          | ~ (v1_funct_1 @ X21))),
% 1.23/1.46      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.23/1.46  thf('22', plain,
% 1.23/1.46      ((~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['20', '21'])).
% 1.23/1.46  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('24', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('26', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 1.23/1.46  thf('27', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.23/1.46         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.23/1.46            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 1.23/1.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['19', '26'])).
% 1.23/1.46  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.23/1.46  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.23/1.46  thf('30', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.23/1.46         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.23/1.46            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.23/1.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.23/1.46  thf('31', plain,
% 1.23/1.46      ((~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.23/1.46            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['10', '30'])).
% 1.23/1.46  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(t61_funct_1, axiom,
% 1.23/1.46    (![A:$i]:
% 1.23/1.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.23/1.46       ( ( v2_funct_1 @ A ) =>
% 1.23/1.46         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.23/1.46             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.23/1.46           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.23/1.46             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.23/1.46  thf('33', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (~ (v2_funct_1 @ X0)
% 1.23/1.46          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.23/1.46              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_relat_1 @ X0))),
% 1.23/1.46      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.23/1.46  thf(redefinition_k6_partfun1, axiom,
% 1.23/1.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.23/1.46  thf('34', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.23/1.46  thf('35', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (~ (v2_funct_1 @ X0)
% 1.23/1.46          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.23/1.46              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_relat_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['33', '34'])).
% 1.23/1.46  thf('36', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(cc2_funct_2, axiom,
% 1.23/1.46    (![A:$i,B:$i,C:$i]:
% 1.23/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.23/1.46       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.23/1.46         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.23/1.46  thf('37', plain,
% 1.23/1.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.23/1.46         (~ (v1_funct_1 @ X15)
% 1.23/1.46          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 1.23/1.46          | (v2_funct_2 @ X15 @ X17)
% 1.23/1.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.23/1.46      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.23/1.46  thf('38', plain,
% 1.23/1.46      (((v2_funct_2 @ sk_B @ sk_A)
% 1.23/1.46        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ~ (v1_funct_1 @ sk_B))),
% 1.23/1.46      inference('sup-', [status(thm)], ['36', '37'])).
% 1.23/1.46  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.23/1.46      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.23/1.46  thf(d3_funct_2, axiom,
% 1.23/1.46    (![A:$i,B:$i]:
% 1.23/1.46     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.23/1.46       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.23/1.46  thf('42', plain,
% 1.23/1.46      (![X18 : $i, X19 : $i]:
% 1.23/1.46         (~ (v2_funct_2 @ X19 @ X18)
% 1.23/1.46          | ((k2_relat_1 @ X19) = (X18))
% 1.23/1.46          | ~ (v5_relat_1 @ X19 @ X18)
% 1.23/1.46          | ~ (v1_relat_1 @ X19))),
% 1.23/1.46      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.23/1.46  thf('43', plain,
% 1.23/1.46      ((~ (v1_relat_1 @ sk_B)
% 1.23/1.46        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.23/1.46        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['41', '42'])).
% 1.23/1.46  thf('44', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(cc1_relset_1, axiom,
% 1.23/1.46    (![A:$i,B:$i,C:$i]:
% 1.23/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.23/1.46       ( v1_relat_1 @ C ) ))).
% 1.23/1.46  thf('45', plain,
% 1.23/1.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.23/1.46         ((v1_relat_1 @ X1)
% 1.23/1.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 1.23/1.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.23/1.46  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 1.23/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.23/1.46  thf('47', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(cc2_relset_1, axiom,
% 1.23/1.46    (![A:$i,B:$i,C:$i]:
% 1.23/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.23/1.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.23/1.46  thf('48', plain,
% 1.23/1.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.23/1.46         ((v5_relat_1 @ X4 @ X6)
% 1.23/1.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.23/1.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.23/1.46  thf('49', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.23/1.46      inference('sup-', [status(thm)], ['47', '48'])).
% 1.23/1.46  thf('50', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.23/1.46  thf('51', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (~ (v2_funct_1 @ X0)
% 1.23/1.46          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.23/1.46              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_relat_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['33', '34'])).
% 1.23/1.46  thf(t29_relset_1, axiom,
% 1.23/1.46    (![A:$i]:
% 1.23/1.46     ( m1_subset_1 @
% 1.23/1.46       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.23/1.46  thf('52', plain,
% 1.23/1.46      (![X14 : $i]:
% 1.23/1.46         (m1_subset_1 @ (k6_relat_1 @ X14) @ 
% 1.23/1.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 1.23/1.46      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.23/1.46  thf('53', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.23/1.46  thf('54', plain,
% 1.23/1.46      (![X14 : $i]:
% 1.23/1.46         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 1.23/1.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 1.23/1.46      inference('demod', [status(thm)], ['52', '53'])).
% 1.23/1.46  thf('55', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.23/1.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.23/1.46          | ~ (v1_relat_1 @ X0)
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v2_funct_1 @ X0))),
% 1.23/1.46      inference('sup+', [status(thm)], ['51', '54'])).
% 1.23/1.46  thf('56', plain,
% 1.23/1.46      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.23/1.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 1.23/1.46        | ~ (v2_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_relat_1 @ sk_B))),
% 1.23/1.46      inference('sup+', [status(thm)], ['50', '55'])).
% 1.23/1.46  thf('57', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.23/1.46  thf('58', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('59', plain,
% 1.23/1.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.23/1.46         (~ (v1_funct_1 @ X15)
% 1.23/1.46          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 1.23/1.46          | (v2_funct_1 @ X15)
% 1.23/1.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.23/1.46      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.23/1.46  thf('60', plain,
% 1.23/1.46      (((v2_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ~ (v1_funct_1 @ sk_B))),
% 1.23/1.46      inference('sup-', [status(thm)], ['58', '59'])).
% 1.23/1.46  thf('61', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 1.23/1.46      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.23/1.46  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 1.23/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.23/1.46  thf('66', plain,
% 1.23/1.46      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.23/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('demod', [status(thm)], ['56', '57', '63', '64', '65'])).
% 1.23/1.46  thf('67', plain,
% 1.23/1.46      (![X14 : $i]:
% 1.23/1.46         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 1.23/1.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 1.23/1.46      inference('demod', [status(thm)], ['52', '53'])).
% 1.23/1.46  thf(redefinition_r2_relset_1, axiom,
% 1.23/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.23/1.46     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.23/1.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.23/1.46       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.23/1.46  thf('68', plain,
% 1.23/1.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.23/1.46         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.23/1.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.23/1.46          | ((X10) = (X13))
% 1.23/1.46          | ~ (r2_relset_1 @ X11 @ X12 @ X10 @ X13))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.23/1.46  thf('69', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i]:
% 1.23/1.46         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 1.23/1.46          | ((k6_partfun1 @ X0) = (X1))
% 1.23/1.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['67', '68'])).
% 1.23/1.46  thf('70', plain,
% 1.23/1.46      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 1.23/1.46        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.23/1.46             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['66', '69'])).
% 1.23/1.46  thf('71', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.23/1.46           (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 1.23/1.46        | ~ (v1_relat_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v2_funct_1 @ sk_B)
% 1.23/1.46        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['35', '70'])).
% 1.23/1.46  thf('72', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['43', '46', '49'])).
% 1.23/1.46  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 1.23/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.23/1.46  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('75', plain, ((v2_funct_1 @ sk_B)),
% 1.23/1.46      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.23/1.46  thf('76', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A))
% 1.23/1.46        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.23/1.46      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 1.23/1.46  thf('77', plain,
% 1.23/1.46      (![X14 : $i]:
% 1.23/1.46         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 1.23/1.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 1.23/1.46      inference('demod', [status(thm)], ['52', '53'])).
% 1.23/1.46  thf('78', plain,
% 1.23/1.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.23/1.46         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.23/1.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.23/1.46          | (r2_relset_1 @ X11 @ X12 @ X10 @ X13)
% 1.23/1.46          | ((X10) != (X13)))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.23/1.46  thf('79', plain,
% 1.23/1.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.23/1.46         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 1.23/1.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.23/1.46      inference('simplify', [status(thm)], ['78'])).
% 1.23/1.46  thf('80', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.23/1.46      inference('sup-', [status(thm)], ['77', '79'])).
% 1.23/1.46  thf('81', plain,
% 1.23/1.46      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['76', '80'])).
% 1.23/1.46  thf('82', plain,
% 1.23/1.46      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.23/1.46         = (k6_partfun1 @ sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['31', '32', '81'])).
% 1.23/1.46  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.23/1.46  thf('84', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A)))
% 1.23/1.46         <= (~
% 1.23/1.46             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46               (k6_partfun1 @ sk_A))))),
% 1.23/1.46      inference('split', [status(esa)], ['0'])).
% 1.23/1.46  thf('85', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.23/1.46            sk_B) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A)))
% 1.23/1.46         <= (~
% 1.23/1.46             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46               (k6_partfun1 @ sk_A))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['83', '84'])).
% 1.23/1.46  thf('86', plain,
% 1.23/1.46      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.23/1.46           (k6_partfun1 @ sk_A)))
% 1.23/1.46         <= (~
% 1.23/1.46             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46               (k6_partfun1 @ sk_A))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['82', '85'])).
% 1.23/1.46  thf('87', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.23/1.46      inference('sup-', [status(thm)], ['77', '79'])).
% 1.23/1.46  thf('88', plain,
% 1.23/1.46      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46         (k6_partfun1 @ sk_A)))),
% 1.23/1.46      inference('demod', [status(thm)], ['86', '87'])).
% 1.23/1.46  thf('89', plain,
% 1.23/1.46      (~
% 1.23/1.46       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.23/1.46         (k6_partfun1 @ sk_A))) | 
% 1.23/1.46       ~
% 1.23/1.46       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.23/1.46          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.23/1.46         (k6_partfun1 @ sk_A)))),
% 1.23/1.46      inference('split', [status(esa)], ['0'])).
% 1.23/1.46  thf('90', plain,
% 1.23/1.46      (~
% 1.23/1.46       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.23/1.46         (k6_partfun1 @ sk_A)))),
% 1.23/1.46      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 1.23/1.46  thf('91', plain,
% 1.23/1.46      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.23/1.46          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.23/1.46          (k6_partfun1 @ sk_A))),
% 1.23/1.46      inference('simpl_trail', [status(thm)], ['9', '90'])).
% 1.23/1.46  thf('92', plain,
% 1.23/1.46      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.23/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 1.23/1.46  thf('93', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.23/1.46  thf('94', plain,
% 1.23/1.46      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.23/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('demod', [status(thm)], ['92', '93'])).
% 1.23/1.46  thf('95', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('96', plain,
% 1.23/1.46      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.23/1.46         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.23/1.46          | ~ (v1_funct_1 @ X22)
% 1.23/1.46          | ~ (v1_funct_1 @ X25)
% 1.23/1.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.23/1.46          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 1.23/1.46              = (k5_relat_1 @ X22 @ X25)))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.23/1.46  thf('97', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.23/1.46         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.23/1.46            = (k5_relat_1 @ sk_B @ X0))
% 1.23/1.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_funct_1 @ sk_B))),
% 1.23/1.46      inference('sup-', [status(thm)], ['95', '96'])).
% 1.23/1.46  thf('98', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('99', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.23/1.46         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.23/1.46            = (k5_relat_1 @ sk_B @ X0))
% 1.23/1.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['97', '98'])).
% 1.23/1.46  thf('100', plain,
% 1.23/1.46      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.23/1.46        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.23/1.46            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['94', '99'])).
% 1.23/1.46  thf('101', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 1.23/1.46  thf('102', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.23/1.46  thf('103', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.23/1.46      inference('demod', [status(thm)], ['101', '102'])).
% 1.23/1.46  thf('104', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(t67_funct_2, axiom,
% 1.23/1.46    (![A:$i,B:$i]:
% 1.23/1.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.23/1.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.23/1.46       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.23/1.46  thf('105', plain,
% 1.23/1.46      (![X31 : $i, X32 : $i]:
% 1.23/1.46         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 1.23/1.46          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.23/1.46          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 1.23/1.46          | ~ (v1_funct_1 @ X32))),
% 1.23/1.46      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.23/1.46  thf('106', plain,
% 1.23/1.46      ((~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.23/1.46        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 1.23/1.46      inference('sup-', [status(thm)], ['104', '105'])).
% 1.23/1.46  thf('107', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('108', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('109', plain,
% 1.23/1.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf(redefinition_k1_relset_1, axiom,
% 1.23/1.46    (![A:$i,B:$i,C:$i]:
% 1.23/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.23/1.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.23/1.46  thf('110', plain,
% 1.23/1.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.23/1.46         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 1.23/1.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.23/1.46  thf('111', plain,
% 1.23/1.46      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.23/1.46      inference('sup-', [status(thm)], ['109', '110'])).
% 1.23/1.46  thf('112', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['106', '107', '108', '111'])).
% 1.23/1.46  thf('113', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (~ (v2_funct_1 @ X0)
% 1.23/1.46          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.23/1.46              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_relat_1 @ X0))),
% 1.23/1.46      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.23/1.46  thf('114', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.23/1.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.23/1.46  thf('115', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (~ (v2_funct_1 @ X0)
% 1.23/1.46          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.23/1.46              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_relat_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['113', '114'])).
% 1.23/1.46  thf('116', plain,
% 1.23/1.46      (![X14 : $i]:
% 1.23/1.46         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 1.23/1.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 1.23/1.46      inference('demod', [status(thm)], ['52', '53'])).
% 1.23/1.46  thf('117', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 1.23/1.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.23/1.46          | ~ (v1_relat_1 @ X0)
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v2_funct_1 @ X0))),
% 1.23/1.46      inference('sup+', [status(thm)], ['115', '116'])).
% 1.23/1.46  thf('118', plain,
% 1.23/1.46      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.23/1.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.23/1.46        | ~ (v2_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_relat_1 @ sk_B))),
% 1.23/1.46      inference('sup+', [status(thm)], ['112', '117'])).
% 1.23/1.46  thf('119', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['106', '107', '108', '111'])).
% 1.23/1.46  thf('120', plain, ((v2_funct_1 @ sk_B)),
% 1.23/1.46      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.23/1.46  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 1.23/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.23/1.46  thf('123', plain,
% 1.23/1.46      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.23/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.23/1.46      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 1.23/1.46  thf('124', plain,
% 1.23/1.46      (![X0 : $i, X1 : $i]:
% 1.23/1.46         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 1.23/1.46          | ((k6_partfun1 @ X0) = (X1))
% 1.23/1.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['67', '68'])).
% 1.23/1.46  thf('125', plain,
% 1.23/1.46      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 1.23/1.46        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.23/1.46             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.23/1.46      inference('sup-', [status(thm)], ['123', '124'])).
% 1.23/1.46  thf('126', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['106', '107', '108', '111'])).
% 1.23/1.46  thf('127', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (~ (v2_funct_1 @ X0)
% 1.23/1.46          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.23/1.46              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v1_relat_1 @ X0))),
% 1.23/1.46      inference('demod', [status(thm)], ['113', '114'])).
% 1.23/1.46  thf('128', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.23/1.46      inference('sup-', [status(thm)], ['77', '79'])).
% 1.23/1.46  thf('129', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.23/1.46           (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.23/1.46           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.23/1.46          | ~ (v1_relat_1 @ X0)
% 1.23/1.46          | ~ (v1_funct_1 @ X0)
% 1.23/1.46          | ~ (v2_funct_1 @ X0))),
% 1.23/1.46      inference('sup+', [status(thm)], ['127', '128'])).
% 1.23/1.46  thf('130', plain,
% 1.23/1.46      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B) @ 
% 1.23/1.46         (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 1.23/1.46         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 1.23/1.46        | ~ (v2_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_funct_1 @ sk_B)
% 1.23/1.46        | ~ (v1_relat_1 @ sk_B))),
% 1.23/1.46      inference('sup+', [status(thm)], ['126', '129'])).
% 1.23/1.46  thf('131', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['106', '107', '108', '111'])).
% 1.23/1.46  thf('132', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['106', '107', '108', '111'])).
% 1.23/1.46  thf('133', plain, ((v2_funct_1 @ sk_B)),
% 1.23/1.46      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.23/1.46  thf('134', plain, ((v1_funct_1 @ sk_B)),
% 1.23/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.23/1.46  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 1.23/1.46      inference('sup-', [status(thm)], ['44', '45'])).
% 1.23/1.46  thf('136', plain,
% 1.23/1.46      ((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.23/1.46        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.23/1.46      inference('demod', [status(thm)],
% 1.23/1.46                ['130', '131', '132', '133', '134', '135'])).
% 1.23/1.46  thf('137', plain,
% 1.23/1.46      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.23/1.46      inference('demod', [status(thm)], ['125', '136'])).
% 1.23/1.46  thf('138', plain,
% 1.23/1.46      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 1.23/1.46         = (k6_partfun1 @ sk_A))),
% 1.23/1.46      inference('demod', [status(thm)], ['100', '103', '137'])).
% 1.23/1.46  thf('139', plain,
% 1.23/1.46      (![X0 : $i]:
% 1.23/1.46         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.23/1.46      inference('sup-', [status(thm)], ['77', '79'])).
% 1.23/1.46  thf('140', plain, ($false),
% 1.23/1.46      inference('demod', [status(thm)], ['91', '138', '139'])).
% 1.23/1.46  
% 1.23/1.46  % SZS output end Refutation
% 1.23/1.46  
% 1.32/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
