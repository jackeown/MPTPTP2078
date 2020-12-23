%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j5KSwBUDR1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:19 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  284 (12656 expanded)
%              Number of leaves         :   36 (3893 expanded)
%              Depth                    :   25
%              Number of atoms          : 2935 (339338 expanded)
%              Number of equality atoms :  104 (1838 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('48',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('49',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('60',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('68',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','60','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('74',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('75',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('76',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('81',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('84',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('85',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('86',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('88',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('90',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('93',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('94',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('95',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('97',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('102',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('103',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('104',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('106',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['79','88','97','106'])).

thf('108',plain,
    ( ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['48','107'])).

thf('109',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('110',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('111',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('112',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
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

thf('115',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('116',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('121',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('122',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('123',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['120','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('129',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('130',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('133',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('134',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['104','105'])).

thf('136',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('137',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['127','130','131','137'])).

thf('139',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['47','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('141',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X30 @ X31 )
        = X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('142',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('146',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('147',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['142','143','144','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('150',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('152',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['139','148','149','150','151'])).

thf('153',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['46','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('155',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('157',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','32','157'])).

thf('159',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('160',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('161',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('163',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('164',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('165',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('166',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','167'])).

thf('169',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['162','168'])).

thf('170',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('171',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('175',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('182',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('183',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('184',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['183','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['182','189'])).

thf('191',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('192',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('193',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('194',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('196',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('197',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('199',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('200',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('202',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('203',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('204',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('205',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('206',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('207',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('208',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('209',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('210',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','112','113','119'])).

thf('211',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('212',plain,(
    ! [X1: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('213',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('214',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['212','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['211','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['210','222'])).

thf('224',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('225',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('226',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('228',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X30 @ X31 )
        = X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('229',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('231',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('232',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['226','232'])).

thf('234',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('235',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('236',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('237',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['223','233','234','235','236'])).

thf('238',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['190','191','197','200','201','202','203','204','205','206','207','208','209','237'])).

thf('239',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['181','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('241',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('243',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['239','240','241','242'])).

thf('244',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['179','180','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','167'])).

thf('246',plain,(
    $false ),
    inference(demod,[status(thm)],['172','244','245'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j5KSwBUDR1
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.65/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.88  % Solved by: fo/fo7.sh
% 0.65/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.88  % done 712 iterations in 0.405s
% 0.65/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.88  % SZS output start Refutation
% 0.65/0.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.65/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.65/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.65/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.65/0.88  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.65/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.65/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.65/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.65/0.88  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.65/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.65/0.88  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.65/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.65/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.65/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.65/0.88  thf(t88_funct_2, conjecture,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( v3_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.65/0.88       ( ( r2_relset_1 @
% 0.65/0.88           A @ A @ 
% 0.65/0.88           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.65/0.88           ( k6_partfun1 @ A ) ) & 
% 0.65/0.88         ( r2_relset_1 @
% 0.65/0.88           A @ A @ 
% 0.65/0.88           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.65/0.88           ( k6_partfun1 @ A ) ) ) ))).
% 0.65/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.88    (~( ![A:$i,B:$i]:
% 0.65/0.88        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.65/0.88            ( v3_funct_2 @ B @ A @ A ) & 
% 0.65/0.88            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.65/0.88          ( ( r2_relset_1 @
% 0.65/0.88              A @ A @ 
% 0.65/0.88              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.65/0.88              ( k6_partfun1 @ A ) ) & 
% 0.65/0.88            ( r2_relset_1 @
% 0.65/0.88              A @ A @ 
% 0.65/0.88              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.65/0.88              ( k6_partfun1 @ A ) ) ) ) )),
% 0.65/0.88    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.65/0.88  thf('0', plain,
% 0.65/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88           (k6_partfun1 @ sk_A))
% 0.65/0.88        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.65/0.88              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.65/0.88             (k6_partfun1 @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('1', plain,
% 0.65/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.65/0.88            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.65/0.88           (k6_partfun1 @ sk_A)))
% 0.65/0.88         <= (~
% 0.65/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.65/0.88                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.65/0.88               (k6_partfun1 @ sk_A))))),
% 0.65/0.88      inference('split', [status(esa)], ['0'])).
% 0.65/0.88  thf('2', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(redefinition_k2_funct_2, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( v3_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.65/0.88       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.65/0.88  thf('3', plain,
% 0.65/0.88      (![X27 : $i, X28 : $i]:
% 0.65/0.88         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 0.65/0.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.65/0.88          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 0.65/0.88          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 0.65/0.88          | ~ (v1_funct_1 @ X27))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.65/0.88  thf('4', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.65/0.88  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('6', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('7', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('9', plain,
% 0.65/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88            sk_B_1) @ 
% 0.65/0.88           (k6_partfun1 @ sk_A)))
% 0.65/0.88         <= (~
% 0.65/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.65/0.88                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.65/0.88               (k6_partfun1 @ sk_A))))),
% 0.65/0.88      inference('demod', [status(thm)], ['1', '8'])).
% 0.65/0.88  thf('10', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(dt_k2_funct_2, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( v3_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.65/0.88       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.65/0.88         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.65/0.88         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.65/0.88         ( m1_subset_1 @
% 0.65/0.88           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.65/0.88  thf('11', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 0.65/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('12', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.65/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.65/0.88  thf('13', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('14', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('15', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('16', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('17', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('18', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(redefinition_k1_partfun1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.65/0.88     ( ( ( v1_funct_1 @ E ) & 
% 0.65/0.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.65/0.88         ( v1_funct_1 @ F ) & 
% 0.65/0.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.65/0.88       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.65/0.88  thf('19', plain,
% 0.65/0.88      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.65/0.88         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.65/0.88          | ~ (v1_funct_1 @ X21)
% 0.65/0.88          | ~ (v1_funct_1 @ X24)
% 0.65/0.88          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.65/0.88          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.65/0.88              = (k5_relat_1 @ X21 @ X24)))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.65/0.88  thf('20', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.65/0.88            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.65/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.65/0.88  thf('21', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('22', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.65/0.88            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.65/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.65/0.88          | ~ (v1_funct_1 @ X0))),
% 0.65/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.65/0.88  thf('23', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88            (k2_funct_1 @ sk_B_1))
% 0.65/0.88            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['17', '22'])).
% 0.65/0.88  thf('24', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('25', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('26', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.65/0.88  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('28', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('29', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.65/0.88  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf(t62_funct_1, axiom,
% 0.65/0.88    (![A:$i]:
% 0.65/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.65/0.88       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.65/0.88  thf('33', plain,
% 0.65/0.88      (![X3 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X3)
% 0.65/0.88          | (v2_funct_1 @ (k2_funct_1 @ X3))
% 0.65/0.88          | ~ (v1_funct_1 @ X3)
% 0.65/0.88          | ~ (v1_relat_1 @ X3))),
% 0.65/0.88      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.65/0.88  thf(dt_k2_funct_1, axiom,
% 0.65/0.88    (![A:$i]:
% 0.65/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.65/0.88       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.65/0.88         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.65/0.88  thf('34', plain,
% 0.65/0.88      (![X1 : $i]:
% 0.65/0.88         ((v1_funct_1 @ (k2_funct_1 @ X1))
% 0.65/0.88          | ~ (v1_funct_1 @ X1)
% 0.65/0.88          | ~ (v1_relat_1 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.65/0.88  thf('35', plain,
% 0.65/0.88      (![X1 : $i]:
% 0.65/0.88         ((v1_relat_1 @ (k2_funct_1 @ X1))
% 0.65/0.88          | ~ (v1_funct_1 @ X1)
% 0.65/0.88          | ~ (v1_relat_1 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.65/0.88  thf(t65_funct_1, axiom,
% 0.65/0.88    (![A:$i]:
% 0.65/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.65/0.88       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.65/0.88  thf('36', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf(t61_funct_1, axiom,
% 0.65/0.88    (![A:$i]:
% 0.65/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.65/0.88       ( ( v2_funct_1 @ A ) =>
% 0.65/0.88         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.65/0.88             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.65/0.88           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.65/0.88             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.65/0.88  thf('37', plain,
% 0.65/0.88      (![X2 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X2)
% 0.65/0.88          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.65/0.88              = (k6_relat_1 @ (k2_relat_1 @ X2)))
% 0.65/0.88          | ~ (v1_funct_1 @ X2)
% 0.65/0.88          | ~ (v1_relat_1 @ X2))),
% 0.65/0.88      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.65/0.88  thf(redefinition_k6_partfun1, axiom,
% 0.65/0.88    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.65/0.88  thf('38', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.65/0.88  thf('39', plain,
% 0.65/0.88      (![X2 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X2)
% 0.65/0.88          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ X2)))
% 0.65/0.88          | ~ (v1_funct_1 @ X2)
% 0.65/0.88          | ~ (v1_relat_1 @ X2))),
% 0.65/0.88      inference('demod', [status(thm)], ['37', '38'])).
% 0.65/0.88  thf('40', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['36', '39'])).
% 0.65/0.88  thf('41', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['35', '40'])).
% 0.65/0.88  thf('42', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['41'])).
% 0.65/0.88  thf('43', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['34', '42'])).
% 0.65/0.88  thf('44', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['43'])).
% 0.65/0.88  thf('45', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['33', '44'])).
% 0.65/0.88  thf('46', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['45'])).
% 0.65/0.88  thf('47', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf('48', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf('49', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('50', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 0.65/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('51', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ 
% 0.65/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['49', '50'])).
% 0.65/0.88  thf('52', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('53', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('54', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((v1_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('55', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.65/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.65/0.88  thf('56', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('57', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('58', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('59', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('60', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.65/0.88  thf('61', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('62', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('63', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.65/0.88      inference('sup-', [status(thm)], ['61', '62'])).
% 0.65/0.88  thf('64', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('65', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('66', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('67', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('68', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.65/0.88  thf('69', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['51', '52', '60', '68'])).
% 0.65/0.88  thf('70', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('71', plain,
% 0.65/0.88      (![X27 : $i, X28 : $i]:
% 0.65/0.88         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 0.65/0.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.65/0.88          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 0.65/0.88          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 0.65/0.88          | ~ (v1_funct_1 @ X27))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.65/0.88  thf('72', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88            = (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.65/0.88  thf('73', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('74', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.65/0.88  thf('75', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.65/0.88  thf('76', plain,
% 0.65/0.88      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.65/0.88  thf('77', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['69', '76'])).
% 0.65/0.88  thf('78', plain,
% 0.65/0.88      (![X27 : $i, X28 : $i]:
% 0.65/0.88         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 0.65/0.88          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.65/0.88          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 0.65/0.88          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 0.65/0.88          | ~ (v1_funct_1 @ X27))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.65/0.88  thf('79', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.65/0.88        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['77', '78'])).
% 0.65/0.88  thf('80', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('81', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('82', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['80', '81'])).
% 0.65/0.88  thf('83', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('84', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.65/0.88  thf('85', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.65/0.88  thf('86', plain,
% 0.65/0.88      ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.65/0.88  thf('87', plain,
% 0.65/0.88      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.65/0.88  thf('88', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['86', '87'])).
% 0.65/0.88  thf('89', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('90', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((v1_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('91', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ 
% 0.65/0.88           sk_A))),
% 0.65/0.88      inference('sup-', [status(thm)], ['89', '90'])).
% 0.65/0.88  thf('92', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('93', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.65/0.88  thf('94', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.65/0.88  thf('95', plain,
% 0.65/0.88      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.65/0.88  thf('96', plain,
% 0.65/0.88      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.65/0.88  thf('97', plain,
% 0.65/0.88      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['95', '96'])).
% 0.65/0.88  thf('98', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('99', plain,
% 0.65/0.88      (![X19 : $i, X20 : $i]:
% 0.65/0.88         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.65/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.65/0.88          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.65/0.88          | ~ (v1_funct_1 @ X20))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.65/0.88  thf('100', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ 
% 0.65/0.88           sk_A))),
% 0.65/0.88      inference('sup-', [status(thm)], ['98', '99'])).
% 0.65/0.88  thf('101', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('102', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.65/0.88  thf('103', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.65/0.88  thf('104', plain,
% 0.65/0.88      ((v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.65/0.88  thf('105', plain,
% 0.65/0.88      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.65/0.88  thf('106', plain,
% 0.65/0.88      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['104', '105'])).
% 0.65/0.88  thf('107', plain,
% 0.65/0.88      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['79', '88', '97', '106'])).
% 0.65/0.88  thf('108', plain,
% 0.65/0.88      ((((k2_funct_2 @ sk_A @ sk_B_1)
% 0.65/0.88          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.65/0.88        | ~ (v1_relat_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup+', [status(thm)], ['48', '107'])).
% 0.65/0.88  thf('109', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('110', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(cc1_relset_1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i]:
% 0.65/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.88       ( v1_relat_1 @ C ) ))).
% 0.65/0.88  thf('111', plain,
% 0.65/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.65/0.88         ((v1_relat_1 @ X5)
% 0.65/0.88          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.65/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.65/0.88  thf('112', plain, ((v1_relat_1 @ sk_B_1)),
% 0.65/0.88      inference('sup-', [status(thm)], ['110', '111'])).
% 0.65/0.88  thf('113', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('114', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(cc2_funct_2, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i]:
% 0.65/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.88       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.65/0.88         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.65/0.88  thf('115', plain,
% 0.65/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.88         (~ (v1_funct_1 @ X16)
% 0.65/0.88          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.65/0.88          | (v2_funct_1 @ X16)
% 0.65/0.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.65/0.88      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.65/0.88  thf('116', plain,
% 0.65/0.88      (((v2_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v1_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup-', [status(thm)], ['114', '115'])).
% 0.65/0.88  thf('117', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('118', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('119', plain, ((v2_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.65/0.88  thf('120', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('121', plain,
% 0.65/0.88      (![X2 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X2)
% 0.65/0.88          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 0.65/0.88              = (k6_relat_1 @ (k1_relat_1 @ X2)))
% 0.65/0.88          | ~ (v1_funct_1 @ X2)
% 0.65/0.88          | ~ (v1_relat_1 @ X2))),
% 0.65/0.88      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.65/0.88  thf('122', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.65/0.88  thf('123', plain,
% 0.65/0.88      (![X2 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X2)
% 0.65/0.88          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 0.65/0.88              = (k6_partfun1 @ (k1_relat_1 @ X2)))
% 0.65/0.88          | ~ (v1_funct_1 @ X2)
% 0.65/0.88          | ~ (v1_relat_1 @ X2))),
% 0.65/0.88      inference('demod', [status(thm)], ['121', '122'])).
% 0.65/0.88  thf('124', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['45'])).
% 0.65/0.88  thf('125', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0))),
% 0.65/0.88      inference('sup+', [status(thm)], ['123', '124'])).
% 0.65/0.88  thf('126', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.65/0.88      inference('simplify', [status(thm)], ['125'])).
% 0.65/0.88  thf('127', plain,
% 0.65/0.88      ((((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.65/0.88          = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))
% 0.65/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('sup+', [status(thm)], ['120', '126'])).
% 0.65/0.88  thf('128', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['69', '76'])).
% 0.65/0.88  thf('129', plain,
% 0.65/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.65/0.88         ((v1_relat_1 @ X5)
% 0.65/0.88          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.65/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.65/0.88  thf('130', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['128', '129'])).
% 0.65/0.88  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['86', '87'])).
% 0.65/0.88  thf('132', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['69', '76'])).
% 0.65/0.88  thf('133', plain,
% 0.65/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.88         (~ (v1_funct_1 @ X16)
% 0.65/0.88          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.65/0.88          | (v2_funct_1 @ X16)
% 0.65/0.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.65/0.88      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.65/0.88  thf('134', plain,
% 0.65/0.88      (((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['132', '133'])).
% 0.65/0.88  thf('135', plain,
% 0.65/0.88      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['104', '105'])).
% 0.65/0.88  thf('136', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['86', '87'])).
% 0.65/0.88  thf('137', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.65/0.88  thf('138', plain,
% 0.65/0.88      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.65/0.88         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['127', '130', '131', '137'])).
% 0.65/0.88  thf('139', plain,
% 0.65/0.88      ((((k6_partfun1 @ (k1_relat_1 @ sk_B_1))
% 0.65/0.88          = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))
% 0.65/0.88        | ~ (v1_relat_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup+', [status(thm)], ['47', '138'])).
% 0.65/0.88  thf('140', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(t67_funct_2, axiom,
% 0.65/0.88    (![A:$i,B:$i]:
% 0.65/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.65/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.65/0.88       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.65/0.88  thf('141', plain,
% 0.65/0.88      (![X30 : $i, X31 : $i]:
% 0.65/0.88         (((k1_relset_1 @ X30 @ X30 @ X31) = (X30))
% 0.65/0.88          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.65/0.88          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.65/0.88          | ~ (v1_funct_1 @ X31))),
% 0.65/0.88      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.65/0.88  thf('142', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.65/0.88        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['140', '141'])).
% 0.65/0.88  thf('143', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('144', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('145', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i]:
% 0.65/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.65/0.88  thf('146', plain,
% 0.65/0.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.65/0.88         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.65/0.88          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.65/0.88  thf('147', plain,
% 0.65/0.88      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.65/0.88      inference('sup-', [status(thm)], ['145', '146'])).
% 0.65/0.88  thf('148', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['142', '143', '144', '147'])).
% 0.65/0.88  thf('149', plain, ((v1_relat_1 @ sk_B_1)),
% 0.65/0.88      inference('sup-', [status(thm)], ['110', '111'])).
% 0.65/0.88  thf('150', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('151', plain, ((v2_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.65/0.88  thf('152', plain,
% 0.65/0.88      (((k6_partfun1 @ sk_A)
% 0.65/0.88         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['139', '148', '149', '150', '151'])).
% 0.65/0.88  thf('153', plain,
% 0.65/0.88      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_relat_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup+', [status(thm)], ['46', '152'])).
% 0.65/0.88  thf('154', plain, ((v1_relat_1 @ sk_B_1)),
% 0.65/0.88      inference('sup-', [status(thm)], ['110', '111'])).
% 0.65/0.88  thf('155', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('156', plain, ((v2_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.65/0.88  thf('157', plain,
% 0.65/0.88      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 0.65/0.88  thf('158', plain,
% 0.65/0.88      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88         (k2_funct_1 @ sk_B_1)) = (k6_partfun1 @ sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['23', '32', '157'])).
% 0.65/0.88  thf('159', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.65/0.88  thf('160', plain,
% 0.65/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88           (k6_partfun1 @ sk_A)))
% 0.65/0.88         <= (~
% 0.65/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88               (k6_partfun1 @ sk_A))))),
% 0.65/0.88      inference('split', [status(esa)], ['0'])).
% 0.65/0.88  thf('161', plain,
% 0.65/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88            (k2_funct_1 @ sk_B_1)) @ 
% 0.65/0.88           (k6_partfun1 @ sk_A)))
% 0.65/0.88         <= (~
% 0.65/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88               (k6_partfun1 @ sk_A))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['159', '160'])).
% 0.65/0.88  thf('162', plain,
% 0.65/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.65/0.88           (k6_partfun1 @ sk_A)))
% 0.65/0.88         <= (~
% 0.65/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88               (k6_partfun1 @ sk_A))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['158', '161'])).
% 0.65/0.88  thf(t29_relset_1, axiom,
% 0.65/0.88    (![A:$i]:
% 0.65/0.88     ( m1_subset_1 @
% 0.65/0.88       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.65/0.88  thf('163', plain,
% 0.65/0.88      (![X15 : $i]:
% 0.65/0.88         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 0.65/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.65/0.88      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.65/0.88  thf('164', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.65/0.88  thf('165', plain,
% 0.65/0.88      (![X15 : $i]:
% 0.65/0.88         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.65/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.65/0.88      inference('demod', [status(thm)], ['163', '164'])).
% 0.65/0.88  thf(reflexivity_r2_relset_1, axiom,
% 0.65/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.88     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.65/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.88       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.65/0.88  thf('166', plain,
% 0.65/0.88      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.88         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.65/0.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.65/0.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.65/0.88      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.65/0.88  thf('167', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.65/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.65/0.88      inference('condensation', [status(thm)], ['166'])).
% 0.65/0.88  thf('168', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['165', '167'])).
% 0.65/0.88  thf('169', plain,
% 0.65/0.88      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88         (k6_partfun1 @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['162', '168'])).
% 0.65/0.88  thf('170', plain,
% 0.65/0.88      (~
% 0.65/0.88       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.65/0.88          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.65/0.88         (k6_partfun1 @ sk_A))) | 
% 0.65/0.88       ~
% 0.65/0.88       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.65/0.88          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.65/0.88         (k6_partfun1 @ sk_A)))),
% 0.65/0.88      inference('split', [status(esa)], ['0'])).
% 0.65/0.88  thf('171', plain,
% 0.65/0.88      (~
% 0.65/0.88       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.65/0.88          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.65/0.88         (k6_partfun1 @ sk_A)))),
% 0.65/0.88      inference('sat_resolution*', [status(thm)], ['169', '170'])).
% 0.65/0.88  thf('172', plain,
% 0.65/0.88      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.65/0.88          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88           sk_B_1) @ 
% 0.65/0.88          (k6_partfun1 @ sk_A))),
% 0.65/0.88      inference('simpl_trail', [status(thm)], ['9', '171'])).
% 0.65/0.88  thf('173', plain,
% 0.65/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('174', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('175', plain,
% 0.65/0.88      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.65/0.88         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.65/0.88          | ~ (v1_funct_1 @ X21)
% 0.65/0.88          | ~ (v1_funct_1 @ X24)
% 0.65/0.88          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.65/0.88          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.65/0.88              = (k5_relat_1 @ X21 @ X24)))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.65/0.88  thf('176', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.65/0.88            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.65/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['174', '175'])).
% 0.65/0.88  thf('177', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('178', plain,
% 0.65/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.88         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.65/0.88            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.65/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.65/0.88          | ~ (v1_funct_1 @ X0))),
% 0.65/0.88      inference('demod', [status(thm)], ['176', '177'])).
% 0.65/0.88  thf('179', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['173', '178'])).
% 0.65/0.88  thf('180', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('181', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf('182', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('183', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf('184', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf('185', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['43'])).
% 0.65/0.88  thf('186', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['184', '185'])).
% 0.65/0.88  thf('187', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['186'])).
% 0.65/0.88  thf('188', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.65/0.88              (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88              = (k6_partfun1 @ 
% 0.65/0.88                 (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['183', '187'])).
% 0.65/0.88  thf('189', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.65/0.88            (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.65/0.88            = (k6_partfun1 @ 
% 0.65/0.88               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['188'])).
% 0.65/0.88  thf('190', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.65/0.88        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))) @ 
% 0.65/0.88            (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))))
% 0.65/0.88            = (k6_partfun1 @ 
% 0.65/0.88               (k2_relat_1 @ 
% 0.65/0.88                (k2_funct_1 @ 
% 0.65/0.88                 (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['182', '189'])).
% 0.65/0.88  thf('191', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('192', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('193', plain,
% 0.65/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.88         (~ (v1_funct_1 @ X16)
% 0.65/0.88          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.65/0.88          | (v2_funct_1 @ X16)
% 0.65/0.88          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.65/0.88      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.65/0.88  thf('194', plain,
% 0.65/0.88      (((v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['192', '193'])).
% 0.65/0.88  thf('195', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.65/0.88  thf('196', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('197', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.65/0.88  thf('198', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('199', plain,
% 0.65/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.65/0.88         ((v1_relat_1 @ X5)
% 0.65/0.88          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.65/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.65/0.88  thf('200', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup-', [status(thm)], ['198', '199'])).
% 0.65/0.88  thf('201', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('202', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.65/0.88  thf('203', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['128', '129'])).
% 0.65/0.88  thf('204', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['86', '87'])).
% 0.65/0.88  thf('205', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('206', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup-', [status(thm)], ['198', '199'])).
% 0.65/0.88  thf('207', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('208', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('209', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('210', plain,
% 0.65/0.88      (((k2_funct_1 @ sk_B_1)
% 0.65/0.88         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('demod', [status(thm)], ['108', '109', '112', '113', '119'])).
% 0.65/0.88  thf('211', plain,
% 0.65/0.88      (![X3 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X3)
% 0.65/0.88          | (v2_funct_1 @ (k2_funct_1 @ X3))
% 0.65/0.88          | ~ (v1_funct_1 @ X3)
% 0.65/0.88          | ~ (v1_relat_1 @ X3))),
% 0.65/0.88      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.65/0.88  thf('212', plain,
% 0.65/0.88      (![X1 : $i]:
% 0.65/0.88         ((v1_funct_1 @ (k2_funct_1 @ X1))
% 0.65/0.88          | ~ (v1_funct_1 @ X1)
% 0.65/0.88          | ~ (v1_relat_1 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.65/0.88  thf('213', plain,
% 0.65/0.88      (![X1 : $i]:
% 0.65/0.88         ((v1_relat_1 @ (k2_funct_1 @ X1))
% 0.65/0.88          | ~ (v1_funct_1 @ X1)
% 0.65/0.88          | ~ (v1_relat_1 @ X1))),
% 0.65/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.65/0.88  thf('214', plain,
% 0.65/0.88      (![X4 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X4)
% 0.65/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.65/0.88          | ~ (v1_funct_1 @ X4)
% 0.65/0.88          | ~ (v1_relat_1 @ X4))),
% 0.65/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.65/0.88  thf('215', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.65/0.88      inference('simplify', [status(thm)], ['125'])).
% 0.65/0.88  thf('216', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.65/0.88      inference('sup+', [status(thm)], ['214', '215'])).
% 0.65/0.88  thf('217', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['213', '216'])).
% 0.65/0.88  thf('218', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['217'])).
% 0.65/0.88  thf('219', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['212', '218'])).
% 0.65/0.88  thf('220', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['219'])).
% 0.65/0.88  thf('221', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 0.65/0.88      inference('sup-', [status(thm)], ['211', '220'])).
% 0.65/0.88  thf('222', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.65/0.88            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.65/0.88          | ~ (v2_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_funct_1 @ X0)
% 0.65/0.88          | ~ (v1_relat_1 @ X0))),
% 0.65/0.88      inference('simplify', [status(thm)], ['221'])).
% 0.65/0.88  thf('223', plain,
% 0.65/0.88      ((((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88          = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))))
% 0.65/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.65/0.88        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.65/0.88      inference('sup+', [status(thm)], ['210', '222'])).
% 0.65/0.88  thf('224', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('225', plain,
% 0.65/0.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.65/0.88         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.65/0.88          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.65/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.65/0.88  thf('226', plain,
% 0.65/0.88      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88         = (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['224', '225'])).
% 0.65/0.88  thf('227', plain,
% 0.65/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.65/0.88      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.65/0.88  thf('228', plain,
% 0.65/0.88      (![X30 : $i, X31 : $i]:
% 0.65/0.88         (((k1_relset_1 @ X30 @ X30 @ X31) = (X30))
% 0.65/0.88          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.65/0.88          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 0.65/0.88          | ~ (v1_funct_1 @ X31))),
% 0.65/0.88      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.65/0.88  thf('229', plain,
% 0.65/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.65/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.65/0.88        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['227', '228'])).
% 0.65/0.88  thf('230', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.65/0.88  thf('231', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.65/0.88      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.65/0.88  thf('232', plain,
% 0.65/0.88      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['229', '230', '231'])).
% 0.65/0.88  thf('233', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.65/0.88      inference('sup+', [status(thm)], ['226', '232'])).
% 0.65/0.88  thf('234', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('sup-', [status(thm)], ['128', '129'])).
% 0.65/0.88  thf('235', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['86', '87'])).
% 0.65/0.88  thf('236', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.65/0.88      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.65/0.88  thf('237', plain,
% 0.65/0.88      (((k6_partfun1 @ sk_A)
% 0.65/0.88         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.65/0.88      inference('demod', [status(thm)], ['223', '233', '234', '235', '236'])).
% 0.65/0.88  thf('238', plain,
% 0.65/0.88      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88         (k2_funct_1 @ (k2_funct_1 @ sk_B_1))) = (k6_partfun1 @ sk_A))),
% 0.65/0.88      inference('demod', [status(thm)],
% 0.65/0.88                ['190', '191', '197', '200', '201', '202', '203', '204', 
% 0.65/0.88                 '205', '206', '207', '208', '209', '237'])).
% 0.65/0.88  thf('239', plain,
% 0.65/0.88      ((((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_partfun1 @ sk_A))
% 0.65/0.88        | ~ (v1_relat_1 @ sk_B_1)
% 0.65/0.88        | ~ (v1_funct_1 @ sk_B_1)
% 0.65/0.88        | ~ (v2_funct_1 @ sk_B_1))),
% 0.65/0.88      inference('sup+', [status(thm)], ['181', '238'])).
% 0.65/0.88  thf('240', plain, ((v1_relat_1 @ sk_B_1)),
% 0.65/0.88      inference('sup-', [status(thm)], ['110', '111'])).
% 0.65/0.88  thf('241', plain, ((v1_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.88  thf('242', plain, ((v2_funct_1 @ sk_B_1)),
% 0.65/0.88      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.65/0.88  thf('243', plain,
% 0.65/0.88      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['239', '240', '241', '242'])).
% 0.65/0.88  thf('244', plain,
% 0.65/0.88      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.65/0.88         sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.65/0.88      inference('demod', [status(thm)], ['179', '180', '243'])).
% 0.65/0.88  thf('245', plain,
% 0.65/0.88      (![X0 : $i]:
% 0.65/0.88         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.65/0.88      inference('sup-', [status(thm)], ['165', '167'])).
% 0.65/0.88  thf('246', plain, ($false),
% 0.65/0.88      inference('demod', [status(thm)], ['172', '244', '245'])).
% 0.65/0.88  
% 0.65/0.88  % SZS output end Refutation
% 0.65/0.88  
% 0.65/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
