%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mzMk0b5yTr

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:15 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  269 (1674 expanded)
%              Number of leaves         :   40 ( 522 expanded)
%              Depth                    :   30
%              Number of atoms          : 2530 (32851 expanded)
%              Number of equality atoms :   84 ( 308 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('16',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X33 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('51',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('52',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != X19 )
      | ( v2_funct_2 @ X20 @ X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('56',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v5_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
      | ( v2_funct_2 @ X20 @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('69',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['64','65','66','72'])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44','47'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('79',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('90',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['75','90'])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('94',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','95','96','97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('101',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('111',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44','47'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('118',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('119',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('120',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('121',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('122',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('127',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','123','124','125','126'])).

thf('128',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','95','96','97','98'])).

thf('134',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X33 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('135',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('139',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('140',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('141',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('144',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('148',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['136','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('152',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('153',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('155',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('159',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('160',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('161',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( k1_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['159','162'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('166',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['157','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('170',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_B ) @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['156','171'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('174',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('175',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('177',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['135','155','177'])).

thf('179',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['132','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('181',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('185',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ sk_A @ sk_A @ X0 @ sk_B )
        = ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ sk_A @ sk_A @ X0 @ sk_B )
        = ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( k1_partfun1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['182','190'])).

thf('192',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('194',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('195',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['193','196'])).

thf('198',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('199',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('200',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('202',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201'])).

thf('203',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('204',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['202','205'])).

thf('207',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('208',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201'])).

thf('209',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('210',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['207','210'])).

thf('212',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('213',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('214',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('216',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['211','212','213','214','215'])).

thf('217',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['206','216'])).

thf('218',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','95','96','97','98'])).

thf('219',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('220',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','217','220'])).

thf('222',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('224',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('227',plain,(
    $false ),
    inference(demod,[status(thm)],['130','225','226'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mzMk0b5yTr
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 571 iterations in 0.293s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.55/0.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.75  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.55/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.75  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.75  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.55/0.75  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.55/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.75  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.55/0.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.75  thf(t88_funct_2, conjecture,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.75         ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.75       ( ( r2_relset_1 @
% 0.55/0.75           A @ A @ 
% 0.55/0.75           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.55/0.75           ( k6_partfun1 @ A ) ) & 
% 0.55/0.75         ( r2_relset_1 @
% 0.55/0.75           A @ A @ 
% 0.55/0.75           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.55/0.75           ( k6_partfun1 @ A ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i,B:$i]:
% 0.55/0.75        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.75            ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.75            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.75          ( ( r2_relset_1 @
% 0.55/0.75              A @ A @ 
% 0.55/0.75              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.55/0.75              ( k6_partfun1 @ A ) ) & 
% 0.55/0.75            ( r2_relset_1 @
% 0.55/0.75              A @ A @ 
% 0.55/0.75              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.55/0.75              ( k6_partfun1 @ A ) ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.55/0.75  thf('0', plain,
% 0.55/0.75      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.75            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.75           (k6_partfun1 @ sk_A))
% 0.55/0.75        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.75              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.75             (k6_partfun1 @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.75            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.75           (k6_partfun1 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.75                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.75               (k6_partfun1 @ sk_A))))),
% 0.55/0.75      inference('split', [status(esa)], ['0'])).
% 0.55/0.75  thf(redefinition_k6_partfun1, axiom,
% 0.55/0.75    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.55/0.75  thf('2', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.75            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.75           (k6_relat_1 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.75                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.75               (k6_partfun1 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.75  thf('4', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(redefinition_k2_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.75         ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.75       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.55/0.75  thf('5', plain,
% 0.55/0.75      (![X29 : $i, X30 : $i]:
% 0.55/0.75         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.55/0.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.55/0.75          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.55/0.75          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.55/0.75          | ~ (v1_funct_1 @ X29))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.75        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.75        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.75  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.75            sk_B) @ 
% 0.55/0.75           (k6_relat_1 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.75               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.75                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.75               (k6_partfun1 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['3', '10'])).
% 0.55/0.75  thf(t61_funct_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v2_funct_1 @ A ) =>
% 0.55/0.75         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.55/0.75             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.55/0.75           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.55/0.75             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('12', plain,
% 0.55/0.75      (![X2 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X2)
% 0.55/0.75          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 0.55/0.75              = (k6_relat_1 @ (k1_relat_1 @ X2)))
% 0.55/0.75          | ~ (v1_funct_1 @ X2)
% 0.55/0.75          | ~ (v1_relat_1 @ X2))),
% 0.55/0.75      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.75  thf(dt_k2_funct_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc2_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.55/0.75         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.55/0.75  thf('15', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         (~ (v1_funct_1 @ X16)
% 0.55/0.75          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.55/0.75          | (v2_funct_2 @ X16 @ X18)
% 0.55/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.55/0.75  thf('16', plain,
% 0.55/0.75      (((v2_funct_2 @ sk_B @ sk_A)
% 0.55/0.75        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.55/0.75  thf('17', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('19', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.55/0.75  thf(d3_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.55/0.75       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i]:
% 0.55/0.75         (~ (v2_funct_2 @ X20 @ X19)
% 0.55/0.75          | ((k2_relat_1 @ X20) = (X19))
% 0.55/0.75          | ~ (v5_relat_1 @ X20 @ X19)
% 0.55/0.75          | ~ (v1_relat_1 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.55/0.75  thf('21', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.75        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.55/0.75        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.75  thf('22', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc1_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( v1_relat_1 @ C ) ))).
% 0.55/0.75  thf('23', plain,
% 0.55/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.75         ((v1_relat_1 @ X3)
% 0.55/0.75          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.75  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.75      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.75  thf('25', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc2_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.75         ((v5_relat_1 @ X6 @ X8)
% 0.55/0.75          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.75  thf('27', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.75  thf('28', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('30', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf(t55_funct_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v2_funct_1 @ A ) =>
% 0.55/0.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.55/0.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('31', plain,
% 0.55/0.75      (![X1 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X1)
% 0.55/0.75          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.55/0.75          | ~ (v1_funct_1 @ X1)
% 0.55/0.75          | ~ (v1_relat_1 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf(t3_funct_2, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v1_funct_1 @ A ) & 
% 0.55/0.75         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.55/0.75         ( m1_subset_1 @
% 0.55/0.75           A @ 
% 0.55/0.75           ( k1_zfmisc_1 @
% 0.55/0.75             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('32', plain,
% 0.55/0.75      (![X32 : $i]:
% 0.55/0.75         ((m1_subset_1 @ X32 @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.55/0.75          | ~ (v1_funct_1 @ X32)
% 0.55/0.75          | ~ (v1_relat_1 @ X32))),
% 0.55/0.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.75  thf('33', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.75  thf('34', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75             (k1_zfmisc_1 @ 
% 0.55/0.75              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.55/0.75               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['30', '33'])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['34'])).
% 0.55/0.75  thf('36', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75             (k1_zfmisc_1 @ 
% 0.55/0.75              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.55/0.75               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['29', '35'])).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['36'])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['28', '37'])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('40', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(t67_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.75       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      (![X33 : $i, X34 : $i]:
% 0.55/0.75         (((k1_relset_1 @ X33 @ X33 @ X34) = (X33))
% 0.55/0.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.55/0.75          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.55/0.75          | ~ (v1_funct_1 @ X34))),
% 0.55/0.75      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.75        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['40', '41'])).
% 0.55/0.75  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('44', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('45', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.55/0.75         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.55/0.75          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.75  thf('48', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['42', '43', '44', '47'])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('50', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      (![X1 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X1)
% 0.55/0.75          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.55/0.75          | ~ (v1_funct_1 @ X1)
% 0.55/0.75          | ~ (v1_relat_1 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('52', plain,
% 0.55/0.75      (![X32 : $i]:
% 0.55/0.75         ((m1_subset_1 @ X32 @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.55/0.75          | ~ (v1_funct_1 @ X32)
% 0.55/0.75          | ~ (v1_relat_1 @ X32))),
% 0.55/0.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.75         ((v5_relat_1 @ X6 @ X8)
% 0.55/0.75          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.75  thf('54', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.75  thf('55', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i]:
% 0.55/0.75         (((k2_relat_1 @ X20) != (X19))
% 0.55/0.75          | (v2_funct_2 @ X20 @ X19)
% 0.55/0.75          | ~ (v5_relat_1 @ X20 @ X19)
% 0.55/0.75          | ~ (v1_relat_1 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.55/0.75  thf('56', plain,
% 0.55/0.75      (![X20 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X20)
% 0.55/0.75          | ~ (v5_relat_1 @ X20 @ (k2_relat_1 @ X20))
% 0.55/0.75          | (v2_funct_2 @ X20 @ (k2_relat_1 @ X20)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['55'])).
% 0.55/0.75  thf('57', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['54', '56'])).
% 0.55/0.75  thf('58', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['57'])).
% 0.55/0.75  thf('59', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['51', '58'])).
% 0.55/0.75  thf('60', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | (v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['50', '59'])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['60'])).
% 0.55/0.75  thf('62', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | (v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['49', '61'])).
% 0.55/0.75  thf('63', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v2_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['62'])).
% 0.55/0.75  thf('64', plain,
% 0.55/0.75      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.55/0.75        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['48', '63'])).
% 0.55/0.75  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.75      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.75  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('67', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('68', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         (~ (v1_funct_1 @ X16)
% 0.55/0.75          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.55/0.75          | (v2_funct_1 @ X16)
% 0.55/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      (((v2_funct_1 @ sk_B)
% 0.55/0.75        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.75  thf('70', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('72', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.75      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.75  thf('73', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)], ['64', '65', '66', '72'])).
% 0.55/0.75  thf('74', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i]:
% 0.55/0.75         (~ (v2_funct_2 @ X20 @ X19)
% 0.55/0.75          | ((k2_relat_1 @ X20) = (X19))
% 0.55/0.75          | ~ (v5_relat_1 @ X20 @ X19)
% 0.55/0.75          | ~ (v1_relat_1 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.75        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.55/0.75        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['73', '74'])).
% 0.55/0.75  thf('76', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['42', '43', '44', '47'])).
% 0.55/0.75  thf('77', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('78', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('79', plain,
% 0.55/0.75      (![X1 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X1)
% 0.55/0.75          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.55/0.75          | ~ (v1_funct_1 @ X1)
% 0.55/0.75          | ~ (v1_relat_1 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('80', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.76  thf('81', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.55/0.76          | ~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v2_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['79', '80'])).
% 0.55/0.76  thf('82', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v2_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0)
% 0.55/0.76          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['78', '81'])).
% 0.55/0.76  thf('83', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.55/0.76          | ~ (v2_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['82'])).
% 0.55/0.76  thf('84', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v2_funct_1 @ X0)
% 0.55/0.76          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['77', '83'])).
% 0.55/0.76  thf('85', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 0.55/0.76          | ~ (v2_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['84'])).
% 0.55/0.76  thf('86', plain,
% 0.55/0.76      (((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.55/0.76        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup+', [status(thm)], ['76', '85'])).
% 0.55/0.76  thf('87', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('89', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('90', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.55/0.76      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.55/0.76  thf('91', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['75', '90'])).
% 0.55/0.76  thf('92', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['39', '91'])).
% 0.55/0.76  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('94', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('95', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.55/0.76  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('98', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('99', plain,
% 0.55/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['38', '95', '96', '97', '98'])).
% 0.55/0.76  thf('100', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(redefinition_k1_partfun1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.76     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.76         ( v1_funct_1 @ F ) & 
% 0.55/0.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.55/0.76       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.55/0.76  thf('101', plain,
% 0.55/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.55/0.76          | ~ (v1_funct_1 @ X23)
% 0.55/0.76          | ~ (v1_funct_1 @ X26)
% 0.55/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.55/0.76          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.55/0.76              = (k5_relat_1 @ X23 @ X26)))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.55/0.76  thf('102', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.55/0.76            = (k5_relat_1 @ sk_B @ X0))
% 0.55/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['100', '101'])).
% 0.55/0.76  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('104', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.55/0.76            = (k5_relat_1 @ sk_B @ X0))
% 0.55/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.76          | ~ (v1_funct_1 @ X0))),
% 0.55/0.76      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.76  thf('105', plain,
% 0.55/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['99', '104'])).
% 0.55/0.76  thf('106', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['13', '105'])).
% 0.55/0.76  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('109', plain,
% 0.55/0.76      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.55/0.76         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.55/0.76  thf('110', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.76  thf('111', plain,
% 0.55/0.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76           (k6_partfun1 @ sk_A)))
% 0.55/0.76         <= (~
% 0.55/0.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76               (k6_partfun1 @ sk_A))))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('112', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.76  thf('113', plain,
% 0.55/0.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76           (k6_relat_1 @ sk_A)))
% 0.55/0.76         <= (~
% 0.55/0.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76               (k6_partfun1 @ sk_A))))),
% 0.55/0.76      inference('demod', [status(thm)], ['111', '112'])).
% 0.55/0.76  thf('114', plain,
% 0.55/0.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76            (k2_funct_1 @ sk_B)) @ 
% 0.55/0.76           (k6_relat_1 @ sk_A)))
% 0.55/0.76         <= (~
% 0.55/0.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76               (k6_partfun1 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['110', '113'])).
% 0.55/0.76  thf('115', plain,
% 0.55/0.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 0.55/0.76         <= (~
% 0.55/0.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76               (k6_partfun1 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['109', '114'])).
% 0.55/0.76  thf('116', plain,
% 0.55/0.76      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.55/0.76            (k6_relat_1 @ sk_A))
% 0.55/0.76         | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76         | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76         | ~ (v2_funct_1 @ sk_B)))
% 0.55/0.76         <= (~
% 0.55/0.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76               (k6_partfun1 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['12', '115'])).
% 0.55/0.76  thf('117', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['42', '43', '44', '47'])).
% 0.55/0.76  thf(dt_k6_partfun1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( m1_subset_1 @
% 0.55/0.76         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.55/0.76       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.55/0.76  thf('118', plain,
% 0.55/0.76      (![X22 : $i]:
% 0.55/0.76         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.55/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.55/0.76  thf('119', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.76  thf('120', plain,
% 0.55/0.76      (![X22 : $i]:
% 0.55/0.76         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.55/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.55/0.76      inference('demod', [status(thm)], ['118', '119'])).
% 0.55/0.76  thf(redefinition_r2_relset_1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.76  thf('121', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.55/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.55/0.76          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.55/0.76          | ((X12) != (X15)))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.55/0.76  thf('122', plain,
% 0.55/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.55/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.55/0.76      inference('simplify', [status(thm)], ['121'])).
% 0.55/0.76  thf('123', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['120', '122'])).
% 0.55/0.76  thf('124', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('126', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('127', plain,
% 0.55/0.76      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76         (k6_partfun1 @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)],
% 0.55/0.76                ['116', '117', '123', '124', '125', '126'])).
% 0.55/0.76  thf('128', plain,
% 0.55/0.76      (~
% 0.55/0.76       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.76          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.76         (k6_partfun1 @ sk_A))) | 
% 0.55/0.76       ~
% 0.55/0.76       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.76          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.76         (k6_partfun1 @ sk_A)))),
% 0.55/0.76      inference('split', [status(esa)], ['0'])).
% 0.55/0.76  thf('129', plain,
% 0.55/0.76      (~
% 0.55/0.76       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.76          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.76         (k6_partfun1 @ sk_A)))),
% 0.55/0.76      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 0.55/0.76  thf('130', plain,
% 0.55/0.76      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.55/0.76          (k6_relat_1 @ sk_A))),
% 0.55/0.76      inference('simpl_trail', [status(thm)], ['11', '129'])).
% 0.55/0.76  thf('131', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.76  thf('132', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.76  thf('133', plain,
% 0.55/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['38', '95', '96', '97', '98'])).
% 0.55/0.76  thf('134', plain,
% 0.55/0.76      (![X33 : $i, X34 : $i]:
% 0.55/0.76         (((k1_relset_1 @ X33 @ X33 @ X34) = (X33))
% 0.55/0.76          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.55/0.76          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.55/0.76          | ~ (v1_funct_1 @ X34))),
% 0.55/0.76      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.55/0.76  thf('135', plain,
% 0.55/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.55/0.76        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['133', '134'])).
% 0.55/0.76  thf('136', plain,
% 0.55/0.76      (![X1 : $i]:
% 0.55/0.76         (~ (v2_funct_1 @ X1)
% 0.55/0.76          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.55/0.76          | ~ (v1_funct_1 @ X1)
% 0.55/0.76          | ~ (v1_relat_1 @ X1))),
% 0.55/0.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.76  thf('137', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.76  thf('138', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.76  thf('139', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.55/0.76  thf('140', plain,
% 0.55/0.76      (![X32 : $i]:
% 0.55/0.76         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 0.55/0.76          | ~ (v1_funct_1 @ X32)
% 0.55/0.76          | ~ (v1_relat_1 @ X32))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.76  thf('141', plain,
% 0.55/0.76      (((v1_funct_2 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76         (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.55/0.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['139', '140'])).
% 0.55/0.76  thf('142', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | (v1_funct_2 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76           (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['138', '141'])).
% 0.55/0.76  thf('143', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('144', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('145', plain,
% 0.55/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | (v1_funct_2 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76           (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.55/0.76  thf('146', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | (v1_funct_2 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76           (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['137', '145'])).
% 0.55/0.76  thf('147', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('148', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('149', plain,
% 0.55/0.76      ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76        (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A)),
% 0.55/0.76      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.55/0.76  thf('150', plain,
% 0.55/0.76      (((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 0.55/0.76        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup+', [status(thm)], ['136', '149'])).
% 0.55/0.76  thf('151', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.55/0.76  thf('152', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('153', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('154', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('155', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.55/0.76      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 0.55/0.76  thf('156', plain,
% 0.55/0.76      (![X1 : $i]:
% 0.55/0.76         (~ (v2_funct_1 @ X1)
% 0.55/0.76          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.55/0.76          | ~ (v1_funct_1 @ X1)
% 0.55/0.76          | ~ (v1_relat_1 @ X1))),
% 0.55/0.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.76  thf('157', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.76  thf('158', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.76  thf('159', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.55/0.76  thf('160', plain,
% 0.55/0.76      (![X32 : $i]:
% 0.55/0.76         ((m1_subset_1 @ X32 @ 
% 0.55/0.76           (k1_zfmisc_1 @ 
% 0.55/0.76            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.55/0.76          | ~ (v1_funct_1 @ X32)
% 0.55/0.76          | ~ (v1_relat_1 @ X32))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.76  thf('161', plain,
% 0.55/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.55/0.76         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.55/0.76          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.76  thf('162', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.55/0.76              = (k1_relat_1 @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['160', '161'])).
% 0.55/0.76  thf('163', plain,
% 0.55/0.76      ((((k1_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ 
% 0.55/0.76          (k2_funct_1 @ sk_B)) = (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.55/0.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['159', '162'])).
% 0.55/0.76  thf('164', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ((k1_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ 
% 0.55/0.76            (k2_funct_1 @ sk_B)) = (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['158', '163'])).
% 0.55/0.76  thf('165', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('166', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('167', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ((k1_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ 
% 0.55/0.76            (k2_funct_1 @ sk_B)) = (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.55/0.76      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.55/0.76  thf('168', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ((k1_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ 
% 0.55/0.76            (k2_funct_1 @ sk_B)) = (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['157', '167'])).
% 0.55/0.76  thf('169', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('170', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('171', plain,
% 0.55/0.76      (((k1_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ 
% 0.55/0.76         (k2_funct_1 @ sk_B)) = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.55/0.76  thf('172', plain,
% 0.55/0.76      ((((k1_relset_1 @ (k2_relat_1 @ sk_B) @ sk_A @ (k2_funct_1 @ sk_B))
% 0.55/0.76          = (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.55/0.76        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup+', [status(thm)], ['156', '171'])).
% 0.55/0.76  thf('173', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.55/0.76  thf('174', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('175', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('176', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('177', plain,
% 0.55/0.76      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.55/0.76         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 0.55/0.76  thf('178', plain,
% 0.55/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['135', '155', '177'])).
% 0.55/0.76  thf('179', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['132', '178'])).
% 0.55/0.76  thf('180', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('181', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('182', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.55/0.76  thf('183', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('184', plain,
% 0.55/0.76      (![X32 : $i]:
% 0.55/0.76         ((m1_subset_1 @ X32 @ 
% 0.55/0.76           (k1_zfmisc_1 @ 
% 0.55/0.76            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.55/0.76          | ~ (v1_funct_1 @ X32)
% 0.55/0.76          | ~ (v1_relat_1 @ X32))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.76  thf('185', plain,
% 0.55/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.55/0.76          | ~ (v1_funct_1 @ X23)
% 0.55/0.76          | ~ (v1_funct_1 @ X26)
% 0.55/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.55/0.76          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.55/0.76              = (k5_relat_1 @ X23 @ X26)))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.55/0.76  thf('186', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 0.55/0.76              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 0.55/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 0.55/0.76          | ~ (v1_funct_1 @ X1)
% 0.55/0.76          | ~ (v1_funct_1 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['184', '185'])).
% 0.55/0.76  thf('187', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.76         (~ (v1_funct_1 @ X1)
% 0.55/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 0.55/0.76          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 0.55/0.76              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['186'])).
% 0.55/0.76  thf('188', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ sk_A @ 
% 0.55/0.76              sk_A @ X0 @ sk_B) = (k5_relat_1 @ X0 @ sk_B))
% 0.55/0.76          | ~ (v1_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['183', '187'])).
% 0.55/0.76  thf('189', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('190', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ sk_A @ 
% 0.55/0.76              sk_A @ X0 @ sk_B) = (k5_relat_1 @ X0 @ sk_B)))),
% 0.55/0.76      inference('demod', [status(thm)], ['188', '189'])).
% 0.55/0.76  thf('191', plain,
% 0.55/0.76      ((((k1_partfun1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ 
% 0.55/0.76          sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.55/0.76          = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.55/0.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['182', '190'])).
% 0.55/0.76  thf('192', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.55/0.76  thf('193', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.55/0.76  thf('194', plain,
% 0.55/0.76      (![X2 : $i]:
% 0.55/0.76         (~ (v2_funct_1 @ X2)
% 0.55/0.76          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.55/0.76              = (k6_relat_1 @ (k2_relat_1 @ X2)))
% 0.55/0.76          | ~ (v1_funct_1 @ X2)
% 0.55/0.76          | ~ (v1_relat_1 @ X2))),
% 0.55/0.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.76  thf('195', plain,
% 0.55/0.76      (![X22 : $i]:
% 0.55/0.76         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.55/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.55/0.76      inference('demod', [status(thm)], ['118', '119'])).
% 0.55/0.76  thf('196', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.55/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.55/0.76          | ~ (v1_relat_1 @ X0)
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v2_funct_1 @ X0))),
% 0.55/0.76      inference('sup+', [status(thm)], ['194', '195'])).
% 0.55/0.76  thf('197', plain,
% 0.55/0.76      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.55/0.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.55/0.76        | ~ (v2_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.76      inference('sup+', [status(thm)], ['193', '196'])).
% 0.55/0.76  thf('198', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.55/0.76  thf('199', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('200', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('201', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('202', plain,
% 0.55/0.76      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['197', '198', '199', '200', '201'])).
% 0.55/0.76  thf('203', plain,
% 0.55/0.76      (![X22 : $i]:
% 0.55/0.76         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.55/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.55/0.76      inference('demod', [status(thm)], ['118', '119'])).
% 0.55/0.76  thf('204', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.55/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.55/0.76          | ((X12) = (X15))
% 0.55/0.76          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.55/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.55/0.76  thf('205', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 0.55/0.76          | ((k6_relat_1 @ X0) = (X1))
% 0.55/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['203', '204'])).
% 0.55/0.76  thf('206', plain,
% 0.55/0.76      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.55/0.76        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.55/0.76             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['202', '205'])).
% 0.55/0.76  thf('207', plain,
% 0.55/0.76      (![X2 : $i]:
% 0.55/0.76         (~ (v2_funct_1 @ X2)
% 0.55/0.76          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.55/0.76              = (k6_relat_1 @ (k2_relat_1 @ X2)))
% 0.55/0.76          | ~ (v1_funct_1 @ X2)
% 0.55/0.76          | ~ (v1_relat_1 @ X2))),
% 0.55/0.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.76  thf('208', plain,
% 0.55/0.76      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['197', '198', '199', '200', '201'])).
% 0.55/0.76  thf('209', plain,
% 0.55/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.55/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.55/0.76      inference('simplify', [status(thm)], ['121'])).
% 0.55/0.76  thf('210', plain,
% 0.55/0.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.76        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.55/0.76        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['208', '209'])).
% 0.55/0.76  thf('211', plain,
% 0.55/0.76      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.55/0.76         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.55/0.76        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup+', [status(thm)], ['207', '210'])).
% 0.55/0.76  thf('212', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.55/0.76  thf('213', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('214', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('215', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.55/0.76  thf('216', plain,
% 0.55/0.76      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.55/0.76        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.55/0.76      inference('demod', [status(thm)], ['211', '212', '213', '214', '215'])).
% 0.55/0.76  thf('217', plain,
% 0.55/0.76      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.55/0.76      inference('demod', [status(thm)], ['206', '216'])).
% 0.55/0.76  thf('218', plain,
% 0.55/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['38', '95', '96', '97', '98'])).
% 0.55/0.76  thf('219', plain,
% 0.55/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.76         ((v1_relat_1 @ X3)
% 0.55/0.76          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.55/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.76  thf('220', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['218', '219'])).
% 0.55/0.76  thf('221', plain,
% 0.55/0.76      ((((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.55/0.76          = (k6_relat_1 @ sk_A))
% 0.55/0.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.76      inference('demod', [status(thm)], ['191', '192', '217', '220'])).
% 0.55/0.76  thf('222', plain,
% 0.55/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.76            sk_B) = (k6_relat_1 @ sk_A)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['131', '221'])).
% 0.55/0.76  thf('223', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.76  thf('224', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('225', plain,
% 0.55/0.76      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.55/0.76         = (k6_relat_1 @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['222', '223', '224'])).
% 0.55/0.76  thf('226', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['120', '122'])).
% 0.55/0.76  thf('227', plain, ($false),
% 0.55/0.76      inference('demod', [status(thm)], ['130', '225', '226'])).
% 0.55/0.76  
% 0.55/0.76  % SZS output end Refutation
% 0.55/0.76  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
