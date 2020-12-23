%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K8YU5mweI8

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:19 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  218 (2057 expanded)
%              Number of leaves         :   36 ( 642 expanded)
%              Depth                    :   15
%              Number of atoms          : 2203 (53736 expanded)
%              Number of equality atoms :   70 ( 323 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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

thf('17',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('52',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('54',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('70',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('80',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['71','72','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['68','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','65','82'])).

thf('84',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','83'])).

thf('85',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('89',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('90',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
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

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('108',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('111',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('112',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('113',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('115',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('119',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('120',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','120'])).

thf('122',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('123',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','120'])).

thf('125',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('128',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('131',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('132',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('135',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('137',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('141',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('142',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('144',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['126','135','144'])).

thf('146',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['123','145'])).

thf('147',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('148',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('149',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('150',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['151','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['150','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['149','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['146','161'])).

thf('163',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('164',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('165',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('169',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('170',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('171',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('173',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171','172'])).

thf('174',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('175',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('176',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('177',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['162','173','174','175','176'])).

thf('178',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['98','178','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K8YU5mweI8
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.66/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.86  % Solved by: fo/fo7.sh
% 0.66/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.86  % done 601 iterations in 0.402s
% 0.66/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.86  % SZS output start Refutation
% 0.66/0.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.66/0.86  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.66/0.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.86  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.86  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.66/0.86  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.66/0.86  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.66/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.86  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.66/0.86  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.66/0.86  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.66/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.86  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.86  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.86  thf(t88_funct_2, conjecture,
% 0.66/0.86    (![A:$i,B:$i]:
% 0.66/0.86     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( v3_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.86       ( ( r2_relset_1 @
% 0.66/0.86           A @ A @ 
% 0.66/0.86           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.66/0.86           ( k6_partfun1 @ A ) ) & 
% 0.66/0.86         ( r2_relset_1 @
% 0.66/0.86           A @ A @ 
% 0.66/0.86           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.66/0.86           ( k6_partfun1 @ A ) ) ) ))).
% 0.66/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.86    (~( ![A:$i,B:$i]:
% 0.66/0.86        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.86            ( v3_funct_2 @ B @ A @ A ) & 
% 0.66/0.86            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.86          ( ( r2_relset_1 @
% 0.66/0.86              A @ A @ 
% 0.66/0.86              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.66/0.86              ( k6_partfun1 @ A ) ) & 
% 0.66/0.86            ( r2_relset_1 @
% 0.66/0.86              A @ A @ 
% 0.66/0.86              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.66/0.86              ( k6_partfun1 @ A ) ) ) ) )),
% 0.66/0.86    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.66/0.86  thf('0', plain,
% 0.66/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.66/0.86           (k6_partfun1 @ sk_A))
% 0.66/0.86        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86             (k6_partfun1 @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('1', plain,
% 0.66/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.66/0.86           (k6_partfun1 @ sk_A)))
% 0.66/0.86         <= (~
% 0.66/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.66/0.86               (k6_partfun1 @ sk_A))))),
% 0.66/0.86      inference('split', [status(esa)], ['0'])).
% 0.66/0.86  thf('2', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(redefinition_k2_funct_2, axiom,
% 0.66/0.86    (![A:$i,B:$i]:
% 0.66/0.86     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( v3_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.86       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.66/0.86  thf('3', plain,
% 0.66/0.86      (![X28 : $i, X29 : $i]:
% 0.66/0.86         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.66/0.86          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.66/0.86          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.66/0.86          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.66/0.86          | ~ (v1_funct_1 @ X28))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.66/0.86  thf('4', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.66/0.86  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.66/0.86  thf('9', plain,
% 0.66/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86            (k2_funct_1 @ sk_B)) @ 
% 0.66/0.86           (k6_partfun1 @ sk_A)))
% 0.66/0.86         <= (~
% 0.66/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.66/0.86               (k6_partfun1 @ sk_A))))),
% 0.66/0.86      inference('demod', [status(thm)], ['1', '8'])).
% 0.66/0.86  thf('10', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('11', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(dt_k2_funct_2, axiom,
% 0.66/0.86    (![A:$i,B:$i]:
% 0.66/0.86     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( v3_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.86       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.66/0.86         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.66/0.86         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.66/0.86         ( m1_subset_1 @
% 0.66/0.86           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.66/0.86  thf('12', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.66/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('13', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.66/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.86  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.66/0.86  thf('18', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf(redefinition_k1_partfun1, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.66/0.86     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.86         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.86         ( v1_funct_1 @ F ) & 
% 0.66/0.86         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.66/0.86       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.66/0.86  thf('19', plain,
% 0.66/0.86      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.66/0.86          | ~ (v1_funct_1 @ X22)
% 0.66/0.86          | ~ (v1_funct_1 @ X25)
% 0.66/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.66/0.86          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.66/0.86              = (k5_relat_1 @ X22 @ X25)))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.66/0.86  thf('20', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.66/0.86            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['18', '19'])).
% 0.66/0.86  thf('21', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('22', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('23', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.86  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('25', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('26', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('27', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.66/0.86  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.66/0.86  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('30', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.66/0.86            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X0))),
% 0.66/0.86      inference('demod', [status(thm)], ['20', '29'])).
% 0.66/0.86  thf('31', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['10', '30'])).
% 0.66/0.86  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('33', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf(cc1_relset_1, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i]:
% 0.66/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.86       ( v1_relat_1 @ C ) ))).
% 0.66/0.86  thf('34', plain,
% 0.66/0.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.86         ((v1_relat_1 @ X4)
% 0.66/0.86          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.66/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.86  thf('35', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['33', '34'])).
% 0.66/0.86  thf(t65_funct_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.86       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.66/0.86  thf('36', plain,
% 0.66/0.86      (![X3 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X3)
% 0.66/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.66/0.86          | ~ (v1_funct_1 @ X3)
% 0.66/0.86          | ~ (v1_relat_1 @ X3))),
% 0.66/0.86      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.66/0.86  thf(t61_funct_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.86       ( ( v2_funct_1 @ A ) =>
% 0.66/0.86         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.66/0.86             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.66/0.86           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.66/0.86             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.66/0.86  thf('37', plain,
% 0.66/0.86      (![X1 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X1)
% 0.66/0.86          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.66/0.86              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X1)
% 0.66/0.86          | ~ (v1_relat_1 @ X1))),
% 0.66/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.66/0.86  thf(redefinition_k6_partfun1, axiom,
% 0.66/0.86    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.66/0.86  thf('38', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.86  thf('39', plain,
% 0.66/0.86      (![X1 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X1)
% 0.66/0.86          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.66/0.86              = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X1)
% 0.66/0.86          | ~ (v1_relat_1 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['37', '38'])).
% 0.66/0.86  thf('40', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.66/0.86      inference('sup+', [status(thm)], ['36', '39'])).
% 0.66/0.86  thf('41', plain,
% 0.66/0.86      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v2_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_relat_1 @ sk_B)
% 0.66/0.86        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['35', '40'])).
% 0.66/0.86  thf('42', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf(cc2_funct_2, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i]:
% 0.66/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.86       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.66/0.86         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.66/0.86  thf('43', plain,
% 0.66/0.86      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (v1_funct_1 @ X15)
% 0.66/0.86          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.66/0.86          | (v2_funct_1 @ X15)
% 0.66/0.86          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.66/0.86      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.66/0.86  thf('44', plain,
% 0.66/0.86      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['42', '43'])).
% 0.66/0.86  thf('45', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('46', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('47', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['45', '46'])).
% 0.66/0.86  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('50', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.66/0.86  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.66/0.86  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('54', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.66/0.86  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('56', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('57', plain,
% 0.66/0.86      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (v1_funct_1 @ X15)
% 0.66/0.86          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.66/0.86          | (v2_funct_1 @ X15)
% 0.66/0.86          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.66/0.86      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.66/0.86  thf('58', plain,
% 0.66/0.86      (((v2_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v1_funct_1 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['56', '57'])).
% 0.66/0.86  thf('59', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('61', plain, ((v2_funct_1 @ sk_B)),
% 0.66/0.86      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.66/0.86  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('63', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('64', plain,
% 0.66/0.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.86         ((v1_relat_1 @ X4)
% 0.66/0.86          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.66/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.86  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.86      inference('sup-', [status(thm)], ['63', '64'])).
% 0.66/0.86  thf('66', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i]:
% 0.66/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.86       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.86  thf('67', plain,
% 0.66/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.86         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.66/0.86          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.86  thf('68', plain,
% 0.66/0.86      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.66/0.86         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['66', '67'])).
% 0.66/0.86  thf('69', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf(t67_funct_2, axiom,
% 0.66/0.86    (![A:$i,B:$i]:
% 0.66/0.86     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.66/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.66/0.86       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.66/0.86  thf('70', plain,
% 0.66/0.86      (![X31 : $i, X32 : $i]:
% 0.66/0.86         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.66/0.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.66/0.86          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.66/0.86          | ~ (v1_funct_1 @ X32))),
% 0.66/0.86      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.66/0.86  thf('71', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['69', '70'])).
% 0.66/0.86  thf('72', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('73', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('74', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('75', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.66/0.86        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['73', '74'])).
% 0.66/0.86  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('77', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('78', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('79', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.66/0.86  thf('80', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.66/0.86  thf('81', plain,
% 0.66/0.86      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.66/0.86      inference('demod', [status(thm)], ['71', '72', '80'])).
% 0.66/0.86  thf('82', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.66/0.86      inference('sup+', [status(thm)], ['68', '81'])).
% 0.66/0.86  thf('83', plain,
% 0.66/0.86      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_partfun1 @ sk_A))),
% 0.66/0.86      inference('demod', [status(thm)],
% 0.66/0.86                ['41', '54', '55', '61', '62', '65', '82'])).
% 0.66/0.86  thf('84', plain,
% 0.66/0.86      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.66/0.86         = (k6_partfun1 @ sk_A))),
% 0.66/0.86      inference('demod', [status(thm)], ['31', '32', '83'])).
% 0.66/0.86  thf('85', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.66/0.86  thf('86', plain,
% 0.66/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86           (k6_partfun1 @ sk_A)))
% 0.66/0.86         <= (~
% 0.66/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86               (k6_partfun1 @ sk_A))))),
% 0.66/0.86      inference('split', [status(esa)], ['0'])).
% 0.66/0.86  thf('87', plain,
% 0.66/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86            sk_B) @ 
% 0.66/0.86           (k6_partfun1 @ sk_A)))
% 0.66/0.86         <= (~
% 0.66/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86               (k6_partfun1 @ sk_A))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['85', '86'])).
% 0.66/0.86  thf('88', plain,
% 0.66/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.66/0.86           (k6_partfun1 @ sk_A)))
% 0.66/0.86         <= (~
% 0.66/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86               (k6_partfun1 @ sk_A))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['84', '87'])).
% 0.66/0.86  thf(t29_relset_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( m1_subset_1 @
% 0.66/0.86       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.66/0.86  thf('89', plain,
% 0.66/0.86      (![X14 : $i]:
% 0.66/0.86         (m1_subset_1 @ (k6_relat_1 @ X14) @ 
% 0.66/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.66/0.86      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.66/0.86  thf('90', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.86  thf('91', plain,
% 0.66/0.86      (![X14 : $i]:
% 0.66/0.86         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 0.66/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.66/0.86      inference('demod', [status(thm)], ['89', '90'])).
% 0.66/0.86  thf(reflexivity_r2_relset_1, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.86     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.86       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.66/0.86  thf('92', plain,
% 0.66/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.86         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.66/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.66/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.66/0.86      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.66/0.86  thf('93', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.66/0.86      inference('condensation', [status(thm)], ['92'])).
% 0.66/0.86  thf('94', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.66/0.86      inference('sup-', [status(thm)], ['91', '93'])).
% 0.66/0.86  thf('95', plain,
% 0.66/0.86      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86         (k6_partfun1 @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['88', '94'])).
% 0.66/0.86  thf('96', plain,
% 0.66/0.86      (~
% 0.66/0.86       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.66/0.86         (k6_partfun1 @ sk_A))) | 
% 0.66/0.86       ~
% 0.66/0.86       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.66/0.86          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.66/0.86         (k6_partfun1 @ sk_A)))),
% 0.66/0.86      inference('split', [status(esa)], ['0'])).
% 0.66/0.86  thf('97', plain,
% 0.66/0.86      (~
% 0.66/0.86       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.66/0.86         (k6_partfun1 @ sk_A)))),
% 0.66/0.86      inference('sat_resolution*', [status(thm)], ['95', '96'])).
% 0.66/0.86  thf('98', plain,
% 0.66/0.86      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.66/0.86          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.66/0.86          (k6_partfun1 @ sk_A))),
% 0.66/0.86      inference('simpl_trail', [status(thm)], ['9', '97'])).
% 0.66/0.86  thf('99', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf('100', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('101', plain,
% 0.66/0.86      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.66/0.86          | ~ (v1_funct_1 @ X22)
% 0.66/0.86          | ~ (v1_funct_1 @ X25)
% 0.66/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.66/0.86          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.66/0.86              = (k5_relat_1 @ X22 @ X25)))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.66/0.86  thf('102', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.66/0.86            = (k5_relat_1 @ sk_B @ X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['100', '101'])).
% 0.66/0.86  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('104', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.66/0.86            = (k5_relat_1 @ sk_B @ X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X0))),
% 0.66/0.86      inference('demod', [status(thm)], ['102', '103'])).
% 0.66/0.86  thf('105', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.66/0.86            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['99', '104'])).
% 0.66/0.86  thf('106', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('107', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf('108', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.66/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('109', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['107', '108'])).
% 0.66/0.86  thf('110', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('111', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.66/0.86  thf('112', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.66/0.86  thf('113', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.66/0.86  thf('114', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf('115', plain,
% 0.66/0.86      (![X28 : $i, X29 : $i]:
% 0.66/0.86         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.66/0.86          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.66/0.86          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.66/0.86          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.66/0.86          | ~ (v1_funct_1 @ X28))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.66/0.86  thf('116', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.66/0.86            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['114', '115'])).
% 0.66/0.86  thf('117', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('118', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.66/0.86  thf('119', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.66/0.86  thf('120', plain,
% 0.66/0.86      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.66/0.86         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.66/0.86  thf('121', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['113', '120'])).
% 0.66/0.86  thf('122', plain,
% 0.66/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.86         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.66/0.86          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.86  thf('123', plain,
% 0.66/0.86      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.66/0.86         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['121', '122'])).
% 0.66/0.86  thf('124', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['113', '120'])).
% 0.66/0.86  thf('125', plain,
% 0.66/0.86      (![X31 : $i, X32 : $i]:
% 0.66/0.86         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.66/0.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.66/0.86          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.66/0.86          | ~ (v1_funct_1 @ X32))),
% 0.66/0.86      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.66/0.86  thf('126', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.66/0.86        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.66/0.86            = (sk_A)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['124', '125'])).
% 0.66/0.86  thf('127', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf('128', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('129', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['127', '128'])).
% 0.66/0.86  thf('130', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('131', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.66/0.86  thf('132', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.66/0.86  thf('133', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.66/0.86  thf('134', plain,
% 0.66/0.86      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.66/0.86         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.66/0.86  thf('135', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['133', '134'])).
% 0.66/0.86  thf('136', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.66/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.66/0.86      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.66/0.86  thf('137', plain,
% 0.66/0.86      (![X18 : $i, X19 : $i]:
% 0.66/0.86         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.66/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.66/0.86          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.66/0.86          | ~ (v1_funct_1 @ X19))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.66/0.86  thf('138', plain,
% 0.66/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.66/0.86        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['136', '137'])).
% 0.66/0.86  thf('139', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('140', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.66/0.86  thf('141', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.66/0.86  thf('142', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.66/0.86  thf('143', plain,
% 0.66/0.86      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.66/0.86         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.66/0.86  thf('144', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['142', '143'])).
% 0.66/0.86  thf('145', plain,
% 0.66/0.86      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.66/0.86         = (sk_A))),
% 0.66/0.86      inference('demod', [status(thm)], ['126', '135', '144'])).
% 0.66/0.86  thf('146', plain,
% 0.66/0.86      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) = (sk_A))),
% 0.66/0.86      inference('sup+', [status(thm)], ['123', '145'])).
% 0.66/0.86  thf('147', plain,
% 0.66/0.86      (![X1 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X1)
% 0.66/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.66/0.86              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X1)
% 0.66/0.86          | ~ (v1_relat_1 @ X1))),
% 0.66/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.66/0.86  thf('148', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.66/0.86  thf('149', plain,
% 0.66/0.86      (![X1 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X1)
% 0.66/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.66/0.86              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X1)
% 0.66/0.86          | ~ (v1_relat_1 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['147', '148'])).
% 0.66/0.86  thf(t62_funct_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.86       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.66/0.86  thf('150', plain,
% 0.66/0.86      (![X2 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X2)
% 0.66/0.86          | (v2_funct_1 @ (k2_funct_1 @ X2))
% 0.66/0.86          | ~ (v1_funct_1 @ X2)
% 0.66/0.86          | ~ (v1_relat_1 @ X2))),
% 0.66/0.86      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.66/0.86  thf(dt_k2_funct_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.66/0.86       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.66/0.86         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.66/0.86  thf('151', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.66/0.86  thf('152', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.66/0.86  thf('153', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.66/0.86      inference('sup+', [status(thm)], ['36', '39'])).
% 0.66/0.86  thf('154', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['152', '153'])).
% 0.66/0.86  thf('155', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0))),
% 0.66/0.86      inference('simplify', [status(thm)], ['154'])).
% 0.66/0.86  thf('156', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['151', '155'])).
% 0.66/0.86  thf('157', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0))),
% 0.66/0.86      inference('simplify', [status(thm)], ['156'])).
% 0.66/0.86  thf('158', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['150', '157'])).
% 0.66/0.86  thf('159', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0))),
% 0.66/0.86      inference('simplify', [status(thm)], ['158'])).
% 0.66/0.86  thf('160', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 0.66/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0))),
% 0.66/0.86      inference('sup+', [status(thm)], ['149', '159'])).
% 0.66/0.86  thf('161', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ((k6_partfun1 @ (k2_relat_1 @ X0))
% 0.66/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.66/0.86      inference('simplify', [status(thm)], ['160'])).
% 0.66/0.86  thf('162', plain,
% 0.66/0.86      ((((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.66/0.86          = (k6_partfun1 @ sk_A))
% 0.66/0.86        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.66/0.86      inference('sup+', [status(thm)], ['146', '161'])).
% 0.66/0.86  thf('163', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['33', '34'])).
% 0.66/0.86  thf('164', plain,
% 0.66/0.86      (![X3 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X3)
% 0.66/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.66/0.86          | ~ (v1_funct_1 @ X3)
% 0.66/0.86          | ~ (v1_relat_1 @ X3))),
% 0.66/0.86      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.66/0.86  thf('165', plain,
% 0.66/0.86      (![X1 : $i]:
% 0.66/0.86         (~ (v2_funct_1 @ X1)
% 0.66/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.66/0.86              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.66/0.86          | ~ (v1_funct_1 @ X1)
% 0.66/0.86          | ~ (v1_relat_1 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['147', '148'])).
% 0.66/0.86  thf('166', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.66/0.86            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.66/0.86          | ~ (v1_relat_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v2_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.66/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.66/0.86      inference('sup+', [status(thm)], ['164', '165'])).
% 0.66/0.86  thf('167', plain,
% 0.66/0.86      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.66/0.86        | ~ (v2_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_funct_1 @ sk_B)
% 0.66/0.86        | ~ (v1_relat_1 @ sk_B)
% 0.66/0.86        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.66/0.86            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['163', '166'])).
% 0.66/0.86  thf('168', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.66/0.86  thf('169', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('170', plain, ((v2_funct_1 @ sk_B)),
% 0.66/0.86      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.66/0.86  thf('171', plain, ((v1_funct_1 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('172', plain, ((v1_relat_1 @ sk_B)),
% 0.66/0.86      inference('sup-', [status(thm)], ['63', '64'])).
% 0.66/0.86  thf('173', plain,
% 0.66/0.86      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.66/0.86         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.66/0.86      inference('demod', [status(thm)],
% 0.66/0.86                ['167', '168', '169', '170', '171', '172'])).
% 0.66/0.86  thf('174', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['33', '34'])).
% 0.66/0.86  thf('175', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.86  thf('176', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.66/0.86  thf('177', plain,
% 0.66/0.86      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_partfun1 @ sk_A))),
% 0.66/0.86      inference('demod', [status(thm)], ['162', '173', '174', '175', '176'])).
% 0.66/0.86  thf('178', plain,
% 0.66/0.86      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.66/0.86         = (k6_partfun1 @ sk_A))),
% 0.66/0.86      inference('demod', [status(thm)], ['105', '106', '177'])).
% 0.66/0.86  thf('179', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.66/0.86      inference('sup-', [status(thm)], ['91', '93'])).
% 0.66/0.86  thf('180', plain, ($false),
% 0.66/0.86      inference('demod', [status(thm)], ['98', '178', '179'])).
% 0.66/0.86  
% 0.66/0.86  % SZS output end Refutation
% 0.66/0.86  
% 0.66/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
