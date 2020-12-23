%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O4yj5dWcQ3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:23 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 617 expanded)
%              Number of leaves         :   38 ( 204 expanded)
%              Depth                    :   18
%              Number of atoms          : 1757 (12878 expanded)
%              Number of equality atoms :   62 ( 144 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('34',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('54',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('55',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('62',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('68',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','65','66','67'])).

thf('69',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('78',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','82'])).

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

thf('89',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('90',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('104',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('105',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('107',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('112',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('113',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['108','109','110','113'])).

thf('115',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('116',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('117',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['108','109','110','113'])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['108','109','110','113'])).

thf('123',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('124',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('126',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['108','109','110','113'])).

thf('128',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('129',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['108','109','110','113'])).

thf('133',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('134',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('136',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','138'])).

thf('140',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('141',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['102','105','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['93','142','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O4yj5dWcQ3
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.15/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.37  % Solved by: fo/fo7.sh
% 1.15/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.37  % done 1285 iterations in 0.866s
% 1.15/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.37  % SZS output start Refutation
% 1.15/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.37  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.15/1.37  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.15/1.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.37  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.15/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.37  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.15/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.37  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.15/1.37  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.15/1.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.15/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.15/1.37  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.15/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.37  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.15/1.37  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.15/1.37  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.15/1.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.15/1.37  thf(t88_funct_2, conjecture,
% 1.15/1.37    (![A:$i,B:$i]:
% 1.15/1.37     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.37       ( ( r2_relset_1 @
% 1.15/1.37           A @ A @ 
% 1.15/1.37           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.15/1.37           ( k6_partfun1 @ A ) ) & 
% 1.15/1.37         ( r2_relset_1 @
% 1.15/1.37           A @ A @ 
% 1.15/1.37           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.15/1.37           ( k6_partfun1 @ A ) ) ) ))).
% 1.15/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.37    (~( ![A:$i,B:$i]:
% 1.15/1.37        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.37            ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.37            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.37          ( ( r2_relset_1 @
% 1.15/1.37              A @ A @ 
% 1.15/1.37              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.15/1.37              ( k6_partfun1 @ A ) ) & 
% 1.15/1.37            ( r2_relset_1 @
% 1.15/1.37              A @ A @ 
% 1.15/1.37              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.15/1.37              ( k6_partfun1 @ A ) ) ) ) )),
% 1.15/1.37    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.15/1.37  thf('0', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A))
% 1.15/1.37        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37             (k6_partfun1 @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('1', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A)))
% 1.15/1.37         <= (~
% 1.15/1.37             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.15/1.37               (k6_partfun1 @ sk_A))))),
% 1.15/1.37      inference('split', [status(esa)], ['0'])).
% 1.15/1.37  thf('2', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(redefinition_k2_funct_2, axiom,
% 1.15/1.37    (![A:$i,B:$i]:
% 1.15/1.37     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.37       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.15/1.37  thf('3', plain,
% 1.15/1.37      (![X29 : $i, X30 : $i]:
% 1.15/1.37         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 1.15/1.37          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.15/1.37          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 1.15/1.37          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 1.15/1.37          | ~ (v1_funct_1 @ X29))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.15/1.37  thf('4', plain,
% 1.15/1.37      ((~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.37  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.37  thf('9', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37            (k2_funct_1 @ sk_B)) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A)))
% 1.15/1.37         <= (~
% 1.15/1.37             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.15/1.37               (k6_partfun1 @ sk_A))))),
% 1.15/1.37      inference('demod', [status(thm)], ['1', '8'])).
% 1.15/1.37  thf('10', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('11', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(dt_k2_funct_2, axiom,
% 1.15/1.37    (![A:$i,B:$i]:
% 1.15/1.37     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( v3_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.37       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.15/1.37         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.15/1.37         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.15/1.37         ( m1_subset_1 @
% 1.15/1.37           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.15/1.37  thf('12', plain,
% 1.15/1.37      (![X21 : $i, X22 : $i]:
% 1.15/1.37         ((m1_subset_1 @ (k2_funct_2 @ X21 @ X22) @ 
% 1.15/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 1.15/1.37          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 1.15/1.37          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.37          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.37          | ~ (v1_funct_1 @ X22))),
% 1.15/1.37      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.15/1.37  thf('13', plain,
% 1.15/1.37      ((~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.15/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.15/1.37  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('17', plain,
% 1.15/1.37      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.15/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 1.15/1.37  thf(redefinition_k1_partfun1, axiom,
% 1.15/1.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.37     ( ( ( v1_funct_1 @ E ) & 
% 1.15/1.37         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.37         ( v1_funct_1 @ F ) & 
% 1.15/1.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.15/1.37       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.15/1.37  thf('18', plain,
% 1.15/1.37      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.37         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.15/1.37          | ~ (v1_funct_1 @ X23)
% 1.15/1.37          | ~ (v1_funct_1 @ X26)
% 1.15/1.37          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.15/1.37          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 1.15/1.37              = (k5_relat_1 @ X23 @ X26)))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.15/1.37  thf('19', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.37         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.15/1.37            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 1.15/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.37          | ~ (v1_funct_1 @ X0)
% 1.15/1.37          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.15/1.37  thf('20', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('21', plain,
% 1.15/1.37      (![X21 : $i, X22 : $i]:
% 1.15/1.37         ((v1_funct_1 @ (k2_funct_2 @ X21 @ X22))
% 1.15/1.37          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 1.15/1.37          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.37          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 1.15/1.37          | ~ (v1_funct_1 @ X22))),
% 1.15/1.37      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.15/1.37  thf('22', plain,
% 1.15/1.37      ((~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['20', '21'])).
% 1.15/1.37  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('24', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('26', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 1.15/1.37  thf('27', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.37         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.15/1.37            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 1.15/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.37          | ~ (v1_funct_1 @ X0))),
% 1.15/1.37      inference('demod', [status(thm)], ['19', '26'])).
% 1.15/1.37  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.37  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.37  thf('30', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.37         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.15/1.37            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.15/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.37          | ~ (v1_funct_1 @ X0))),
% 1.15/1.37      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.15/1.37  thf('31', plain,
% 1.15/1.37      ((~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.15/1.37            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['10', '30'])).
% 1.15/1.37  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(t61_funct_1, axiom,
% 1.15/1.37    (![A:$i]:
% 1.15/1.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.37       ( ( v2_funct_1 @ A ) =>
% 1.15/1.37         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.15/1.37             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.15/1.37           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.15/1.37             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.37  thf('33', plain,
% 1.15/1.37      (![X4 : $i]:
% 1.15/1.37         (~ (v2_funct_1 @ X4)
% 1.15/1.37          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.15/1.37              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.15/1.37          | ~ (v1_funct_1 @ X4)
% 1.15/1.37          | ~ (v1_relat_1 @ X4))),
% 1.15/1.37      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.37  thf(redefinition_k6_partfun1, axiom,
% 1.15/1.37    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.15/1.37  thf('34', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.37  thf('35', plain,
% 1.15/1.37      (![X4 : $i]:
% 1.15/1.37         (~ (v2_funct_1 @ X4)
% 1.15/1.37          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.15/1.37              = (k6_partfun1 @ (k2_relat_1 @ X4)))
% 1.15/1.37          | ~ (v1_funct_1 @ X4)
% 1.15/1.37          | ~ (v1_relat_1 @ X4))),
% 1.15/1.37      inference('demod', [status(thm)], ['33', '34'])).
% 1.15/1.37  thf('36', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(cc2_funct_2, axiom,
% 1.15/1.37    (![A:$i,B:$i,C:$i]:
% 1.15/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.37       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.15/1.37         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.15/1.37  thf('37', plain,
% 1.15/1.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.15/1.37         (~ (v1_funct_1 @ X16)
% 1.15/1.37          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 1.15/1.37          | (v2_funct_2 @ X16 @ X18)
% 1.15/1.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.15/1.37      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.15/1.37  thf('38', plain,
% 1.15/1.37      (((v2_funct_2 @ sk_B @ sk_A)
% 1.15/1.37        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ~ (v1_funct_1 @ sk_B))),
% 1.15/1.37      inference('sup-', [status(thm)], ['36', '37'])).
% 1.15/1.37  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.15/1.37      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.15/1.37  thf(d3_funct_2, axiom,
% 1.15/1.37    (![A:$i,B:$i]:
% 1.15/1.37     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.15/1.37       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.15/1.37  thf('42', plain,
% 1.15/1.37      (![X19 : $i, X20 : $i]:
% 1.15/1.37         (~ (v2_funct_2 @ X20 @ X19)
% 1.15/1.37          | ((k2_relat_1 @ X20) = (X19))
% 1.15/1.37          | ~ (v5_relat_1 @ X20 @ X19)
% 1.15/1.37          | ~ (v1_relat_1 @ X20))),
% 1.15/1.37      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.15/1.37  thf('43', plain,
% 1.15/1.37      ((~ (v1_relat_1 @ sk_B)
% 1.15/1.37        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.15/1.37        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['41', '42'])).
% 1.15/1.37  thf('44', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(cc2_relat_1, axiom,
% 1.15/1.37    (![A:$i]:
% 1.15/1.37     ( ( v1_relat_1 @ A ) =>
% 1.15/1.37       ( ![B:$i]:
% 1.15/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.15/1.37  thf('45', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i]:
% 1.15/1.37         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.15/1.37          | (v1_relat_1 @ X0)
% 1.15/1.37          | ~ (v1_relat_1 @ X1))),
% 1.15/1.37      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.37  thf('46', plain,
% 1.15/1.37      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.15/1.37      inference('sup-', [status(thm)], ['44', '45'])).
% 1.15/1.37  thf(fc6_relat_1, axiom,
% 1.15/1.37    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.15/1.37  thf('47', plain,
% 1.15/1.37      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.15/1.37      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.37  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['46', '47'])).
% 1.15/1.37  thf('49', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(cc2_relset_1, axiom,
% 1.15/1.37    (![A:$i,B:$i,C:$i]:
% 1.15/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.37       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.15/1.37  thf('50', plain,
% 1.15/1.37      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.15/1.37         ((v5_relat_1 @ X5 @ X7)
% 1.15/1.37          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.15/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.37  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.15/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.15/1.37  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.15/1.37  thf('53', plain,
% 1.15/1.37      (![X4 : $i]:
% 1.15/1.37         (~ (v2_funct_1 @ X4)
% 1.15/1.37          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.15/1.37              = (k6_partfun1 @ (k2_relat_1 @ X4)))
% 1.15/1.37          | ~ (v1_funct_1 @ X4)
% 1.15/1.37          | ~ (v1_relat_1 @ X4))),
% 1.15/1.37      inference('demod', [status(thm)], ['33', '34'])).
% 1.15/1.37  thf(t29_relset_1, axiom,
% 1.15/1.37    (![A:$i]:
% 1.15/1.37     ( m1_subset_1 @
% 1.15/1.37       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.15/1.37  thf('54', plain,
% 1.15/1.37      (![X15 : $i]:
% 1.15/1.37         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 1.15/1.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.37      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.15/1.37  thf('55', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.37  thf('56', plain,
% 1.15/1.37      (![X15 : $i]:
% 1.15/1.37         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.37      inference('demod', [status(thm)], ['54', '55'])).
% 1.15/1.37  thf('57', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.15/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.15/1.37          | ~ (v1_relat_1 @ X0)
% 1.15/1.37          | ~ (v1_funct_1 @ X0)
% 1.15/1.37          | ~ (v2_funct_1 @ X0))),
% 1.15/1.37      inference('sup+', [status(thm)], ['53', '56'])).
% 1.15/1.37  thf('58', plain,
% 1.15/1.37      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.15/1.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 1.15/1.37        | ~ (v2_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_relat_1 @ sk_B))),
% 1.15/1.37      inference('sup+', [status(thm)], ['52', '57'])).
% 1.15/1.37  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.15/1.37  thf('60', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('61', plain,
% 1.15/1.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.15/1.37         (~ (v1_funct_1 @ X16)
% 1.15/1.37          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 1.15/1.37          | (v2_funct_1 @ X16)
% 1.15/1.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.15/1.37      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.15/1.37  thf('62', plain,
% 1.15/1.37      (((v2_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ~ (v1_funct_1 @ sk_B))),
% 1.15/1.37      inference('sup-', [status(thm)], ['60', '61'])).
% 1.15/1.37  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.37  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['46', '47'])).
% 1.15/1.37  thf('68', plain,
% 1.15/1.37      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.15/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 1.15/1.37  thf('69', plain,
% 1.15/1.37      (![X15 : $i]:
% 1.15/1.37         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.37      inference('demod', [status(thm)], ['54', '55'])).
% 1.15/1.37  thf(redefinition_r2_relset_1, axiom,
% 1.15/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.37     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.37         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.37       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.15/1.37  thf('70', plain,
% 1.15/1.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.15/1.37         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.15/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.15/1.37          | ((X11) = (X14))
% 1.15/1.37          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.15/1.37  thf('71', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i]:
% 1.15/1.37         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 1.15/1.37          | ((k6_partfun1 @ X0) = (X1))
% 1.15/1.37          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 1.15/1.37      inference('sup-', [status(thm)], ['69', '70'])).
% 1.15/1.37  thf('72', plain,
% 1.15/1.37      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 1.15/1.37        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.37             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['68', '71'])).
% 1.15/1.37  thf('73', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.37           (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 1.15/1.37        | ~ (v1_relat_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v2_funct_1 @ sk_B)
% 1.15/1.37        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['35', '72'])).
% 1.15/1.37  thf('74', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.15/1.37  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['46', '47'])).
% 1.15/1.37  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('77', plain, ((v2_funct_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.37  thf('78', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A))
% 1.15/1.37        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.15/1.37      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.15/1.37  thf('79', plain,
% 1.15/1.37      (![X15 : $i]:
% 1.15/1.37         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.37      inference('demod', [status(thm)], ['54', '55'])).
% 1.15/1.37  thf('80', plain,
% 1.15/1.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.15/1.37         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.15/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.15/1.37          | (r2_relset_1 @ X12 @ X13 @ X11 @ X14)
% 1.15/1.37          | ((X11) != (X14)))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.15/1.37  thf('81', plain,
% 1.15/1.37      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.15/1.37         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 1.15/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.15/1.37      inference('simplify', [status(thm)], ['80'])).
% 1.15/1.37  thf('82', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.15/1.37      inference('sup-', [status(thm)], ['79', '81'])).
% 1.15/1.37  thf('83', plain,
% 1.15/1.37      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['78', '82'])).
% 1.15/1.37  thf('84', plain,
% 1.15/1.37      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.15/1.37         = (k6_partfun1 @ sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['31', '32', '83'])).
% 1.15/1.37  thf('85', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.37  thf('86', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A)))
% 1.15/1.37         <= (~
% 1.15/1.37             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37               (k6_partfun1 @ sk_A))))),
% 1.15/1.37      inference('split', [status(esa)], ['0'])).
% 1.15/1.37  thf('87', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.15/1.37            sk_B) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A)))
% 1.15/1.37         <= (~
% 1.15/1.37             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37               (k6_partfun1 @ sk_A))))),
% 1.15/1.37      inference('sup-', [status(thm)], ['85', '86'])).
% 1.15/1.37  thf('88', plain,
% 1.15/1.37      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.37           (k6_partfun1 @ sk_A)))
% 1.15/1.37         <= (~
% 1.15/1.37             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37               (k6_partfun1 @ sk_A))))),
% 1.15/1.37      inference('sup-', [status(thm)], ['84', '87'])).
% 1.15/1.37  thf('89', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.15/1.37      inference('sup-', [status(thm)], ['79', '81'])).
% 1.15/1.37  thf('90', plain,
% 1.15/1.37      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37         (k6_partfun1 @ sk_A)))),
% 1.15/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.37  thf('91', plain,
% 1.15/1.37      (~
% 1.15/1.37       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.15/1.37         (k6_partfun1 @ sk_A))) | 
% 1.15/1.37       ~
% 1.15/1.37       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.15/1.37          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.15/1.37         (k6_partfun1 @ sk_A)))),
% 1.15/1.37      inference('split', [status(esa)], ['0'])).
% 1.15/1.37  thf('92', plain,
% 1.15/1.37      (~
% 1.15/1.37       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.15/1.37         (k6_partfun1 @ sk_A)))),
% 1.15/1.37      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 1.15/1.37  thf('93', plain,
% 1.15/1.37      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.15/1.37          (k6_partfun1 @ sk_A))),
% 1.15/1.37      inference('simpl_trail', [status(thm)], ['9', '92'])).
% 1.15/1.37  thf('94', plain,
% 1.15/1.37      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.15/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 1.15/1.37  thf('95', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.37  thf('96', plain,
% 1.15/1.37      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.15/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('demod', [status(thm)], ['94', '95'])).
% 1.15/1.37  thf('97', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('98', plain,
% 1.15/1.37      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.37         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.15/1.37          | ~ (v1_funct_1 @ X23)
% 1.15/1.37          | ~ (v1_funct_1 @ X26)
% 1.15/1.37          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.15/1.37          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 1.15/1.37              = (k5_relat_1 @ X23 @ X26)))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.15/1.37  thf('99', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.37         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.15/1.37            = (k5_relat_1 @ sk_B @ X0))
% 1.15/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.37          | ~ (v1_funct_1 @ X0)
% 1.15/1.37          | ~ (v1_funct_1 @ sk_B))),
% 1.15/1.37      inference('sup-', [status(thm)], ['97', '98'])).
% 1.15/1.37  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('101', plain,
% 1.15/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.37         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.15/1.37            = (k5_relat_1 @ sk_B @ X0))
% 1.15/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.37          | ~ (v1_funct_1 @ X0))),
% 1.15/1.37      inference('demod', [status(thm)], ['99', '100'])).
% 1.15/1.37  thf('102', plain,
% 1.15/1.37      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.15/1.37        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.15/1.37            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.15/1.37      inference('sup-', [status(thm)], ['96', '101'])).
% 1.15/1.37  thf('103', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 1.15/1.37  thf('104', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.15/1.37  thf('105', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.15/1.37      inference('demod', [status(thm)], ['103', '104'])).
% 1.15/1.37  thf('106', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(t67_funct_2, axiom,
% 1.15/1.37    (![A:$i,B:$i]:
% 1.15/1.37     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.15/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.15/1.37       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.15/1.37  thf('107', plain,
% 1.15/1.37      (![X32 : $i, X33 : $i]:
% 1.15/1.37         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 1.15/1.37          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 1.15/1.37          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 1.15/1.37          | ~ (v1_funct_1 @ X33))),
% 1.15/1.37      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.15/1.37  thf('108', plain,
% 1.15/1.37      ((~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.15/1.37        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['106', '107'])).
% 1.15/1.37  thf('109', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('110', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('111', plain,
% 1.15/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf(redefinition_k1_relset_1, axiom,
% 1.15/1.37    (![A:$i,B:$i,C:$i]:
% 1.15/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.37       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.15/1.37  thf('112', plain,
% 1.15/1.37      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.15/1.37         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.15/1.37          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.15/1.37  thf('113', plain,
% 1.15/1.37      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.15/1.37      inference('sup-', [status(thm)], ['111', '112'])).
% 1.15/1.37  thf('114', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['108', '109', '110', '113'])).
% 1.15/1.37  thf('115', plain,
% 1.15/1.37      (![X4 : $i]:
% 1.15/1.37         (~ (v2_funct_1 @ X4)
% 1.15/1.37          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.15/1.37              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 1.15/1.37          | ~ (v1_funct_1 @ X4)
% 1.15/1.37          | ~ (v1_relat_1 @ X4))),
% 1.15/1.37      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.37  thf('116', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.37  thf('117', plain,
% 1.15/1.37      (![X4 : $i]:
% 1.15/1.37         (~ (v2_funct_1 @ X4)
% 1.15/1.37          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.15/1.37              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 1.15/1.37          | ~ (v1_funct_1 @ X4)
% 1.15/1.37          | ~ (v1_relat_1 @ X4))),
% 1.15/1.37      inference('demod', [status(thm)], ['115', '116'])).
% 1.15/1.37  thf('118', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.15/1.37      inference('sup-', [status(thm)], ['79', '81'])).
% 1.15/1.37  thf('119', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 1.15/1.37           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 1.15/1.37           (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.15/1.37          | ~ (v1_relat_1 @ X0)
% 1.15/1.37          | ~ (v1_funct_1 @ X0)
% 1.15/1.37          | ~ (v2_funct_1 @ X0))),
% 1.15/1.37      inference('sup+', [status(thm)], ['117', '118'])).
% 1.15/1.37  thf('120', plain,
% 1.15/1.37      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B) @ 
% 1.15/1.37         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.15/1.37         (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 1.15/1.37        | ~ (v2_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_relat_1 @ sk_B))),
% 1.15/1.37      inference('sup+', [status(thm)], ['114', '119'])).
% 1.15/1.37  thf('121', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['108', '109', '110', '113'])).
% 1.15/1.37  thf('122', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['108', '109', '110', '113'])).
% 1.15/1.37  thf('123', plain, ((v2_funct_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.37  thf('124', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('125', plain, ((v1_relat_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['46', '47'])).
% 1.15/1.37  thf('126', plain,
% 1.15/1.37      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_partfun1 @ sk_A))),
% 1.15/1.37      inference('demod', [status(thm)],
% 1.15/1.37                ['120', '121', '122', '123', '124', '125'])).
% 1.15/1.37  thf('127', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['108', '109', '110', '113'])).
% 1.15/1.37  thf('128', plain,
% 1.15/1.37      (![X4 : $i]:
% 1.15/1.37         (~ (v2_funct_1 @ X4)
% 1.15/1.37          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.15/1.37              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 1.15/1.37          | ~ (v1_funct_1 @ X4)
% 1.15/1.37          | ~ (v1_relat_1 @ X4))),
% 1.15/1.37      inference('demod', [status(thm)], ['115', '116'])).
% 1.15/1.37  thf('129', plain,
% 1.15/1.37      (![X15 : $i]:
% 1.15/1.37         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.37      inference('demod', [status(thm)], ['54', '55'])).
% 1.15/1.37  thf('130', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 1.15/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.15/1.37          | ~ (v1_relat_1 @ X0)
% 1.15/1.37          | ~ (v1_funct_1 @ X0)
% 1.15/1.37          | ~ (v2_funct_1 @ X0))),
% 1.15/1.37      inference('sup+', [status(thm)], ['128', '129'])).
% 1.15/1.37  thf('131', plain,
% 1.15/1.37      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.15/1.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.15/1.37        | ~ (v2_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_funct_1 @ sk_B)
% 1.15/1.37        | ~ (v1_relat_1 @ sk_B))),
% 1.15/1.37      inference('sup+', [status(thm)], ['127', '130'])).
% 1.15/1.37  thf('132', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['108', '109', '110', '113'])).
% 1.15/1.37  thf('133', plain, ((v2_funct_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.37  thf('134', plain, ((v1_funct_1 @ sk_B)),
% 1.15/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.37  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 1.15/1.37      inference('demod', [status(thm)], ['46', '47'])).
% 1.15/1.37  thf('136', plain,
% 1.15/1.37      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.15/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.37      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 1.15/1.37  thf('137', plain,
% 1.15/1.37      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.15/1.37         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.15/1.37          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.15/1.37          | ((X11) = (X14))
% 1.15/1.37          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 1.15/1.37      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.15/1.37  thf('138', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.37             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ X0)
% 1.15/1.37          | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (X0))
% 1.15/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.37      inference('sup-', [status(thm)], ['136', '137'])).
% 1.15/1.37  thf('139', plain,
% 1.15/1.37      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.15/1.37        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_partfun1 @ sk_A)))),
% 1.15/1.37      inference('sup-', [status(thm)], ['126', '138'])).
% 1.15/1.37  thf('140', plain,
% 1.15/1.37      (![X15 : $i]:
% 1.15/1.37         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.15/1.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.15/1.37      inference('demod', [status(thm)], ['54', '55'])).
% 1.15/1.37  thf('141', plain,
% 1.15/1.37      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_partfun1 @ sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['139', '140'])).
% 1.15/1.37  thf('142', plain,
% 1.15/1.37      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 1.15/1.37         = (k6_partfun1 @ sk_A))),
% 1.15/1.37      inference('demod', [status(thm)], ['102', '105', '141'])).
% 1.15/1.37  thf('143', plain,
% 1.15/1.37      (![X0 : $i]:
% 1.15/1.37         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.15/1.37      inference('sup-', [status(thm)], ['79', '81'])).
% 1.15/1.37  thf('144', plain, ($false),
% 1.15/1.37      inference('demod', [status(thm)], ['93', '142', '143'])).
% 1.15/1.37  
% 1.15/1.37  % SZS output end Refutation
% 1.15/1.37  
% 1.15/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
