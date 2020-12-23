%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H93c9bR6Vn

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:17 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 480 expanded)
%              Number of leaves         :   37 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          : 1523 (10773 expanded)
%              Number of equality atoms :   47 (  92 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('39',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('40',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('43',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','54'])).

thf('56',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('57',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('58',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','54'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('65',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('71',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','68','69','70'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['72'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','54'])).

thf('77',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('78',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('80',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','80'])).

thf('82',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('86',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('96',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('99',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('104',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['100','101','102','105'])).

thf('107',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('108',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['72'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['106','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['100','101','102','105'])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['100','101','102','105'])).

thf('117',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('118',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('120',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['84','97','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H93c9bR6Vn
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 856 iterations in 0.689s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.91/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.91/1.14  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.14  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.91/1.14  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.91/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.91/1.14  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.91/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.91/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.14  thf(t88_funct_2, conjecture,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( v3_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.91/1.14       ( ( r2_relset_1 @
% 0.91/1.14           A @ A @ 
% 0.91/1.14           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.91/1.14           ( k6_partfun1 @ A ) ) & 
% 0.91/1.14         ( r2_relset_1 @
% 0.91/1.14           A @ A @ 
% 0.91/1.14           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.91/1.14           ( k6_partfun1 @ A ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.14    (~( ![A:$i,B:$i]:
% 0.91/1.14        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.91/1.14            ( v3_funct_2 @ B @ A @ A ) & 
% 0.91/1.14            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.91/1.14          ( ( r2_relset_1 @
% 0.91/1.14              A @ A @ 
% 0.91/1.14              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.91/1.14              ( k6_partfun1 @ A ) ) & 
% 0.91/1.14            ( r2_relset_1 @
% 0.91/1.14              A @ A @ 
% 0.91/1.14              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.91/1.14              ( k6_partfun1 @ A ) ) ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.91/1.14  thf('0', plain,
% 0.91/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.91/1.14           (k6_partfun1 @ sk_A))
% 0.91/1.14        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14             (k6_partfun1 @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.91/1.14           (k6_partfun1 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.91/1.14               (k6_partfun1 @ sk_A))))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('2', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(redefinition_k2_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( v3_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.91/1.14       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.91/1.14  thf('3', plain,
% 0.91/1.14      (![X29 : $i, X30 : $i]:
% 0.91/1.14         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.91/1.14          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.91/1.14          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.91/1.14          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.91/1.14          | ~ (v1_funct_1 @ X29))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.91/1.14  thf('4', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('6', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('7', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14            (k2_funct_1 @ sk_B_1)) @ 
% 0.91/1.14           (k6_partfun1 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.91/1.14               (k6_partfun1 @ sk_A))))),
% 0.91/1.14      inference('demod', [status(thm)], ['1', '8'])).
% 0.91/1.14  thf('10', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(dt_k2_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( v3_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.91/1.14       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.91/1.14         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.91/1.14         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.91/1.14         ( m1_subset_1 @
% 0.91/1.14           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      (![X21 : $i, X22 : $i]:
% 0.91/1.14         ((m1_subset_1 @ (k2_funct_2 @ X21 @ X22) @ 
% 0.91/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.91/1.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.91/1.14          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.91/1.14          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.91/1.14          | ~ (v1_funct_1 @ X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.91/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.14  thf('14', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('15', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('16', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('17', plain,
% 0.91/1.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.91/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.91/1.14  thf(redefinition_k1_partfun1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.14         ( v1_funct_1 @ F ) & 
% 0.91/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.14       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.91/1.14          | ~ (v1_funct_1 @ X23)
% 0.91/1.14          | ~ (v1_funct_1 @ X26)
% 0.91/1.14          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.91/1.14          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.91/1.14              = (k5_relat_1 @ X23 @ X26)))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.91/1.14  thf('19', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 0.91/1.14            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 0.91/1.14            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.14  thf('20', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      (![X21 : $i, X22 : $i]:
% 0.91/1.14         ((v1_funct_1 @ (k2_funct_2 @ X21 @ X22))
% 0.91/1.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.91/1.14          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.91/1.14          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.91/1.14          | ~ (v1_funct_1 @ X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.14  thf('23', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('24', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('25', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('26', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 0.91/1.14            (k2_funct_2 @ sk_A @ sk_B_1) @ X0)
% 0.91/1.14            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['19', '26'])).
% 0.91/1.14  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.91/1.14  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.91/1.14            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.91/1.14            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['10', '30'])).
% 0.91/1.14  thf('32', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.91/1.14         sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['31', '32'])).
% 0.91/1.14  thf('34', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14           (k6_partfun1 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14               (k6_partfun1 @ sk_A))))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('36', plain,
% 0.91/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.91/1.14            sk_B_1) @ 
% 0.91/1.14           (k6_partfun1 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14               (k6_partfun1 @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14           (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_partfun1 @ sk_A)))
% 0.91/1.14         <= (~
% 0.91/1.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14               (k6_partfun1 @ sk_A))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['33', '36'])).
% 0.91/1.14  thf(t61_funct_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.14       ( ( v2_funct_1 @ A ) =>
% 0.91/1.14         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.91/1.14             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.91/1.14           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.91/1.14             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.91/1.14  thf('38', plain,
% 0.91/1.14      (![X1 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X1)
% 0.91/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.91/1.14              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.91/1.14  thf(redefinition_k6_partfun1, axiom,
% 0.91/1.14    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.91/1.14  thf('39', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.14  thf('40', plain,
% 0.91/1.14      (![X1 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X1)
% 0.91/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.91/1.14              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['38', '39'])).
% 0.91/1.14  thf('41', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(cc2_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.91/1.14         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.91/1.14  thf('42', plain,
% 0.91/1.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         (~ (v1_funct_1 @ X16)
% 0.91/1.14          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.91/1.14          | (v2_funct_2 @ X16 @ X18)
% 0.91/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.91/1.14  thf('43', plain,
% 0.91/1.14      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 0.91/1.14        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['41', '42'])).
% 0.91/1.14  thf('44', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('46', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 0.91/1.14      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.91/1.14  thf(d3_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.91/1.14       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.91/1.14  thf('47', plain,
% 0.91/1.14      (![X19 : $i, X20 : $i]:
% 0.91/1.14         (~ (v2_funct_2 @ X20 @ X19)
% 0.91/1.14          | ((k2_relat_1 @ X20) = (X19))
% 0.91/1.14          | ~ (v5_relat_1 @ X20 @ X19)
% 0.91/1.14          | ~ (v1_relat_1 @ X20))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      ((~ (v1_relat_1 @ sk_B_1)
% 0.91/1.14        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 0.91/1.14        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(cc1_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( v1_relat_1 @ C ) ))).
% 0.91/1.14  thf('50', plain,
% 0.91/1.14      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.14         ((v1_relat_1 @ X2)
% 0.91/1.14          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.14  thf('51', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.14  thf('52', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(cc2_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.14  thf('53', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         ((v5_relat_1 @ X5 @ X7)
% 0.91/1.14          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.14  thf('54', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 0.91/1.14      inference('sup-', [status(thm)], ['52', '53'])).
% 0.91/1.14  thf('55', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['48', '51', '54'])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      (![X1 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X1)
% 0.91/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.91/1.14              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['38', '39'])).
% 0.91/1.14  thf(t29_relset_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( m1_subset_1 @
% 0.91/1.14       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.91/1.14  thf('57', plain,
% 0.91/1.14      (![X15 : $i]:
% 0.91/1.14         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 0.91/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.91/1.14      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.91/1.14  thf('58', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.14  thf('59', plain,
% 0.91/1.14      (![X15 : $i]:
% 0.91/1.14         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.91/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.91/1.14      inference('demod', [status(thm)], ['57', '58'])).
% 0.91/1.14  thf('60', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.91/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v2_funct_1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['56', '59'])).
% 0.91/1.14  thf('61', plain,
% 0.91/1.14      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))
% 0.91/1.14        | ~ (v2_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['55', '60'])).
% 0.91/1.14  thf('62', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['48', '51', '54'])).
% 0.91/1.14  thf('63', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('64', plain,
% 0.91/1.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         (~ (v1_funct_1 @ X16)
% 0.91/1.14          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.91/1.14          | (v2_funct_1 @ X16)
% 0.91/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.91/1.14  thf('65', plain,
% 0.91/1.14      (((v2_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['63', '64'])).
% 0.91/1.14  thf('66', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('67', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('68', plain, ((v2_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.91/1.14  thf('69', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.14  thf('71', plain,
% 0.91/1.14      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('demod', [status(thm)], ['61', '62', '68', '69', '70'])).
% 0.91/1.14  thf(reflexivity_r2_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.14       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.14         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.91/1.14          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.91/1.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.91/1.14      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.91/1.14  thf('73', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.91/1.14      inference('condensation', [status(thm)], ['72'])).
% 0.91/1.14  thf('74', plain,
% 0.91/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['71', '73'])).
% 0.91/1.14  thf('75', plain,
% 0.91/1.14      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14         (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14         (k6_partfun1 @ (k2_relat_1 @ sk_B_1)))
% 0.91/1.14        | ~ (v1_relat_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['40', '74'])).
% 0.91/1.14  thf('76', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['48', '51', '54'])).
% 0.91/1.14  thf('77', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.14  thf('78', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('79', plain, ((v2_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.91/1.14  thf('80', plain,
% 0.91/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14        (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) @ (k6_partfun1 @ sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.91/1.14  thf('81', plain,
% 0.91/1.14      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14         (k6_partfun1 @ sk_A)))),
% 0.91/1.14      inference('demod', [status(thm)], ['37', '80'])).
% 0.91/1.14  thf('82', plain,
% 0.91/1.14      (~
% 0.91/1.14       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.91/1.14         (k6_partfun1 @ sk_A))) | 
% 0.91/1.14       ~
% 0.91/1.14       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.91/1.14          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.91/1.14         (k6_partfun1 @ sk_A)))),
% 0.91/1.14      inference('split', [status(esa)], ['0'])).
% 0.91/1.14  thf('83', plain,
% 0.91/1.14      (~
% 0.91/1.14       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.91/1.14         (k6_partfun1 @ sk_A)))),
% 0.91/1.14      inference('sat_resolution*', [status(thm)], ['81', '82'])).
% 0.91/1.14  thf('84', plain,
% 0.91/1.14      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.14          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14           (k2_funct_1 @ sk_B_1)) @ 
% 0.91/1.14          (k6_partfun1 @ sk_A))),
% 0.91/1.14      inference('simpl_trail', [status(thm)], ['9', '83'])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.91/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.91/1.14  thf('86', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.91/1.14  thf('87', plain,
% 0.91/1.14      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.91/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('demod', [status(thm)], ['85', '86'])).
% 0.91/1.14  thf('88', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('89', plain,
% 0.91/1.14      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.91/1.14          | ~ (v1_funct_1 @ X23)
% 0.91/1.14          | ~ (v1_funct_1 @ X26)
% 0.91/1.14          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.91/1.14          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.91/1.14              = (k5_relat_1 @ X23 @ X26)))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.91/1.14  thf('90', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.91/1.14            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v1_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['88', '89'])).
% 0.91/1.14  thf('91', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('92', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.91/1.14            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['90', '91'])).
% 0.91/1.14  thf('93', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.91/1.14        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14            (k2_funct_1 @ sk_B_1))
% 0.91/1.14            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['87', '92'])).
% 0.91/1.14  thf('94', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.91/1.14  thf('95', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.91/1.14  thf('96', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['94', '95'])).
% 0.91/1.14  thf('97', plain,
% 0.91/1.14      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.91/1.14         (k2_funct_1 @ sk_B_1)) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.91/1.14      inference('demod', [status(thm)], ['93', '96'])).
% 0.91/1.14  thf('98', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(t67_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.91/1.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.91/1.14       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.91/1.14  thf('99', plain,
% 0.91/1.14      (![X32 : $i, X33 : $i]:
% 0.91/1.14         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.91/1.14          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.91/1.14          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.91/1.14          | ~ (v1_funct_1 @ X33))),
% 0.91/1.14      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.91/1.14  thf('100', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.91/1.14        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['98', '99'])).
% 0.91/1.14  thf('101', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('102', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('103', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.14  thf('104', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.14         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.91/1.14          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.14  thf('105', plain,
% 0.91/1.14      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['103', '104'])).
% 0.91/1.14  thf('106', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.91/1.14      inference('demod', [status(thm)], ['100', '101', '102', '105'])).
% 0.91/1.14  thf('107', plain,
% 0.91/1.14      (![X1 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X1)
% 0.91/1.14          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.91/1.14              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.91/1.14  thf('108', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.14  thf('109', plain,
% 0.91/1.14      (![X1 : $i]:
% 0.91/1.14         (~ (v2_funct_1 @ X1)
% 0.91/1.14          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.91/1.14              = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['107', '108'])).
% 0.91/1.14  thf('110', plain,
% 0.91/1.14      (![X15 : $i]:
% 0.91/1.14         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.91/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.91/1.14      inference('demod', [status(thm)], ['57', '58'])).
% 0.91/1.14  thf('111', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.91/1.14      inference('condensation', [status(thm)], ['72'])).
% 0.91/1.14  thf('112', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['110', '111'])).
% 0.91/1.14  thf('113', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.91/1.14           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 0.91/1.14           (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v2_funct_1 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['109', '112'])).
% 0.91/1.14  thf('114', plain,
% 0.91/1.14      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B_1) @ 
% 0.91/1.14         (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.91/1.14         (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 0.91/1.14        | ~ (v2_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_B_1)
% 0.91/1.14        | ~ (v1_relat_1 @ sk_B_1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['106', '113'])).
% 0.91/1.15  thf('115', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.91/1.15      inference('demod', [status(thm)], ['100', '101', '102', '105'])).
% 0.91/1.15  thf('116', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.91/1.15      inference('demod', [status(thm)], ['100', '101', '102', '105'])).
% 0.91/1.15  thf('117', plain, ((v2_funct_1 @ sk_B_1)),
% 0.91/1.15      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.91/1.15  thf('118', plain, ((v1_funct_1 @ sk_B_1)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('119', plain, ((v1_relat_1 @ sk_B_1)),
% 0.91/1.15      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('120', plain,
% 0.91/1.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.15        (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) @ (k6_partfun1 @ sk_A))),
% 0.91/1.15      inference('demod', [status(thm)],
% 0.91/1.15                ['114', '115', '116', '117', '118', '119'])).
% 0.91/1.15  thf('121', plain, ($false),
% 0.91/1.15      inference('demod', [status(thm)], ['84', '97', '120'])).
% 0.91/1.15  
% 0.91/1.15  % SZS output end Refutation
% 0.91/1.15  
% 0.98/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
