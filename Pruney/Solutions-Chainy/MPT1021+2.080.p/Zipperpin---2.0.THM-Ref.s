%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FWMTvC7YNf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:24 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 646 expanded)
%              Number of leaves         :   36 ( 211 expanded)
%              Depth                    :   17
%              Number of atoms          : 1597 (14615 expanded)
%              Number of equality atoms :   44 (  99 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('42',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('61',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('62',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('63',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('70',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','73','74','75'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','56','59'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('85',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('88',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('98',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','98'])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','99'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('103',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('104',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('113',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('115',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['104','113','114'])).

thf('116',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('122',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('124',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['117','122','125'])).

thf('127',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['101','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('129',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('134',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('136',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['100','131','134','135','136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FWMTvC7YNf
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.12/2.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.33  % Solved by: fo/fo7.sh
% 2.12/2.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.33  % done 1525 iterations in 1.879s
% 2.12/2.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.33  % SZS output start Refutation
% 2.12/2.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.12/2.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.12/2.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.12/2.33  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.12/2.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.12/2.33  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 2.12/2.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.12/2.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.12/2.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.12/2.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.12/2.33  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.12/2.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.12/2.33  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.12/2.33  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.12/2.33  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.12/2.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.12/2.33  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.33  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.12/2.33  thf(sk_B_type, type, sk_B: $i).
% 2.12/2.33  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 2.12/2.33  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.12/2.33  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.12/2.33  thf(t61_funct_1, axiom,
% 2.12/2.33    (![A:$i]:
% 2.12/2.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.12/2.33       ( ( v2_funct_1 @ A ) =>
% 2.12/2.33         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.12/2.33             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.12/2.33           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.12/2.33             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.12/2.33  thf('0', plain,
% 2.12/2.33      (![X5 : $i]:
% 2.12/2.33         (~ (v2_funct_1 @ X5)
% 2.12/2.33          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 2.12/2.33              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 2.12/2.33          | ~ (v1_funct_1 @ X5)
% 2.12/2.33          | ~ (v1_relat_1 @ X5))),
% 2.12/2.33      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.12/2.33  thf(redefinition_k6_partfun1, axiom,
% 2.12/2.33    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.12/2.33  thf('1', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 2.12/2.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.12/2.33  thf('2', plain,
% 2.12/2.33      (![X5 : $i]:
% 2.12/2.33         (~ (v2_funct_1 @ X5)
% 2.12/2.33          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 2.12/2.33              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 2.12/2.33          | ~ (v1_funct_1 @ X5)
% 2.12/2.33          | ~ (v1_relat_1 @ X5))),
% 2.12/2.33      inference('demod', [status(thm)], ['0', '1'])).
% 2.12/2.33  thf(t88_funct_2, conjecture,
% 2.12/2.33    (![A:$i,B:$i]:
% 2.12/2.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.12/2.33         ( v3_funct_2 @ B @ A @ A ) & 
% 2.12/2.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.12/2.33       ( ( r2_relset_1 @
% 2.12/2.33           A @ A @ 
% 2.12/2.33           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 2.12/2.33           ( k6_partfun1 @ A ) ) & 
% 2.12/2.33         ( r2_relset_1 @
% 2.12/2.33           A @ A @ 
% 2.12/2.33           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 2.12/2.33           ( k6_partfun1 @ A ) ) ) ))).
% 2.12/2.34  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.34    (~( ![A:$i,B:$i]:
% 2.12/2.34        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.12/2.34            ( v3_funct_2 @ B @ A @ A ) & 
% 2.12/2.34            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.12/2.34          ( ( r2_relset_1 @
% 2.12/2.34              A @ A @ 
% 2.12/2.34              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 2.12/2.34              ( k6_partfun1 @ A ) ) & 
% 2.12/2.34            ( r2_relset_1 @
% 2.12/2.34              A @ A @ 
% 2.12/2.34              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 2.12/2.34              ( k6_partfun1 @ A ) ) ) ) )),
% 2.12/2.34    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 2.12/2.34  thf('3', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.12/2.34           (k6_partfun1 @ sk_A))
% 2.12/2.34        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34             (k6_partfun1 @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('4', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.12/2.34           (k6_partfun1 @ sk_A)))
% 2.12/2.34         <= (~
% 2.12/2.34             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.12/2.34               (k6_partfun1 @ sk_A))))),
% 2.12/2.34      inference('split', [status(esa)], ['3'])).
% 2.12/2.34  thf('5', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf(redefinition_k2_funct_2, axiom,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.12/2.34         ( v3_funct_2 @ B @ A @ A ) & 
% 2.12/2.34         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.12/2.34       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 2.12/2.34  thf('6', plain,
% 2.12/2.34      (![X27 : $i, X28 : $i]:
% 2.12/2.34         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 2.12/2.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 2.12/2.34          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 2.12/2.34          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 2.12/2.34          | ~ (v1_funct_1 @ X27))),
% 2.12/2.34      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 2.12/2.34  thf('7', plain,
% 2.12/2.34      ((~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['5', '6'])).
% 2.12/2.34  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.12/2.34  thf('12', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34            (k2_funct_1 @ sk_B)) @ 
% 2.12/2.34           (k6_partfun1 @ sk_A)))
% 2.12/2.34         <= (~
% 2.12/2.34             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.12/2.34               (k6_partfun1 @ sk_A))))),
% 2.12/2.34      inference('demod', [status(thm)], ['4', '11'])).
% 2.12/2.34  thf('13', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('14', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf(dt_k2_funct_2, axiom,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.12/2.34         ( v3_funct_2 @ B @ A @ A ) & 
% 2.12/2.34         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.12/2.34       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 2.12/2.34         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 2.12/2.34         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 2.12/2.34         ( m1_subset_1 @
% 2.12/2.34           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 2.12/2.34  thf('15', plain,
% 2.12/2.34      (![X19 : $i, X20 : $i]:
% 2.12/2.34         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 2.12/2.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 2.12/2.34          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 2.12/2.34          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 2.12/2.34          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 2.12/2.34          | ~ (v1_funct_1 @ X20))),
% 2.12/2.34      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 2.12/2.34  thf('16', plain,
% 2.12/2.34      ((~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 2.12/2.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.12/2.34      inference('sup-', [status(thm)], ['14', '15'])).
% 2.12/2.34  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.12/2.34  thf('21', plain,
% 2.12/2.34      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 2.12/2.34  thf(redefinition_k1_partfun1, axiom,
% 2.12/2.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.12/2.34     ( ( ( v1_funct_1 @ E ) & 
% 2.12/2.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.12/2.34         ( v1_funct_1 @ F ) & 
% 2.12/2.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.12/2.34       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.12/2.34  thf('22', plain,
% 2.12/2.34      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.12/2.34         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.12/2.34          | ~ (v1_funct_1 @ X21)
% 2.12/2.34          | ~ (v1_funct_1 @ X24)
% 2.12/2.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.12/2.34          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 2.12/2.34              = (k5_relat_1 @ X21 @ X24)))),
% 2.12/2.34      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.12/2.34  thf('23', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 2.12/2.34            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 2.12/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.12/2.34          | ~ (v1_funct_1 @ X0)
% 2.12/2.34          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['21', '22'])).
% 2.12/2.34  thf('24', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('25', plain,
% 2.12/2.34      (![X19 : $i, X20 : $i]:
% 2.12/2.34         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 2.12/2.34          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 2.12/2.34          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 2.12/2.34          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 2.12/2.34          | ~ (v1_funct_1 @ X20))),
% 2.12/2.34      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 2.12/2.34  thf('26', plain,
% 2.12/2.34      ((~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['24', '25'])).
% 2.12/2.34  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.12/2.34  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.12/2.34  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['30', '31'])).
% 2.12/2.34  thf('33', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 2.12/2.34            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 2.12/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.12/2.34          | ~ (v1_funct_1 @ X0))),
% 2.12/2.34      inference('demod', [status(thm)], ['23', '32'])).
% 2.12/2.34  thf('34', plain,
% 2.12/2.34      ((~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['13', '33'])).
% 2.12/2.34  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('36', plain,
% 2.12/2.34      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 2.12/2.34         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['34', '35'])).
% 2.12/2.34  thf('37', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.12/2.34  thf('38', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34           (k6_partfun1 @ sk_A)))
% 2.12/2.34         <= (~
% 2.12/2.34             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34               (k6_partfun1 @ sk_A))))),
% 2.12/2.34      inference('split', [status(esa)], ['3'])).
% 2.12/2.34  thf('39', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34            sk_B) @ 
% 2.12/2.34           (k6_partfun1 @ sk_A)))
% 2.12/2.34         <= (~
% 2.12/2.34             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34               (k6_partfun1 @ sk_A))))),
% 2.12/2.34      inference('sup-', [status(thm)], ['37', '38'])).
% 2.12/2.34  thf('40', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_partfun1 @ sk_A)))
% 2.12/2.34         <= (~
% 2.12/2.34             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34               (k6_partfun1 @ sk_A))))),
% 2.12/2.34      inference('sup-', [status(thm)], ['36', '39'])).
% 2.12/2.34  thf('41', plain,
% 2.12/2.34      (![X5 : $i]:
% 2.12/2.34         (~ (v2_funct_1 @ X5)
% 2.12/2.34          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 2.12/2.34              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 2.12/2.34          | ~ (v1_funct_1 @ X5)
% 2.12/2.34          | ~ (v1_relat_1 @ X5))),
% 2.12/2.34      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.12/2.34  thf('42', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 2.12/2.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.12/2.34  thf('43', plain,
% 2.12/2.34      (![X5 : $i]:
% 2.12/2.34         (~ (v2_funct_1 @ X5)
% 2.12/2.34          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 2.12/2.34              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 2.12/2.34          | ~ (v1_funct_1 @ X5)
% 2.12/2.34          | ~ (v1_relat_1 @ X5))),
% 2.12/2.34      inference('demod', [status(thm)], ['41', '42'])).
% 2.12/2.34  thf('44', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf(cc2_funct_2, axiom,
% 2.12/2.34    (![A:$i,B:$i,C:$i]:
% 2.12/2.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.12/2.34       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 2.12/2.34         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 2.12/2.34  thf('45', plain,
% 2.12/2.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.12/2.34         (~ (v1_funct_1 @ X14)
% 2.12/2.34          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 2.12/2.34          | (v2_funct_2 @ X14 @ X16)
% 2.12/2.34          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_funct_2])).
% 2.12/2.34  thf('46', plain,
% 2.12/2.34      (((v2_funct_2 @ sk_B @ sk_A)
% 2.12/2.34        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v1_funct_1 @ sk_B))),
% 2.12/2.34      inference('sup-', [status(thm)], ['44', '45'])).
% 2.12/2.34  thf('47', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('49', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 2.12/2.34      inference('demod', [status(thm)], ['46', '47', '48'])).
% 2.12/2.34  thf(d3_funct_2, axiom,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.12/2.34       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.12/2.34  thf('50', plain,
% 2.12/2.34      (![X17 : $i, X18 : $i]:
% 2.12/2.34         (~ (v2_funct_2 @ X18 @ X17)
% 2.12/2.34          | ((k2_relat_1 @ X18) = (X17))
% 2.12/2.34          | ~ (v5_relat_1 @ X18 @ X17)
% 2.12/2.34          | ~ (v1_relat_1 @ X18))),
% 2.12/2.34      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.12/2.34  thf('51', plain,
% 2.12/2.34      ((~ (v1_relat_1 @ sk_B)
% 2.12/2.34        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 2.12/2.34        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['49', '50'])).
% 2.12/2.34  thf('52', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf(cc2_relat_1, axiom,
% 2.12/2.34    (![A:$i]:
% 2.12/2.34     ( ( v1_relat_1 @ A ) =>
% 2.12/2.34       ( ![B:$i]:
% 2.12/2.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.12/2.34  thf('53', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.12/2.34          | (v1_relat_1 @ X0)
% 2.12/2.34          | ~ (v1_relat_1 @ X1))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.12/2.34  thf('54', plain,
% 2.12/2.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 2.12/2.34      inference('sup-', [status(thm)], ['52', '53'])).
% 2.12/2.34  thf(fc6_relat_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.12/2.34  thf('55', plain,
% 2.12/2.34      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.12/2.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.12/2.34  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['54', '55'])).
% 2.12/2.34  thf('57', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf(cc2_relset_1, axiom,
% 2.12/2.34    (![A:$i,B:$i,C:$i]:
% 2.12/2.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.12/2.34       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.12/2.34  thf('58', plain,
% 2.12/2.34      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.12/2.34         ((v5_relat_1 @ X6 @ X8)
% 2.12/2.34          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.12/2.34  thf('59', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 2.12/2.34      inference('sup-', [status(thm)], ['57', '58'])).
% 2.12/2.34  thf('60', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['51', '56', '59'])).
% 2.12/2.34  thf('61', plain,
% 2.12/2.34      (![X5 : $i]:
% 2.12/2.34         (~ (v2_funct_1 @ X5)
% 2.12/2.34          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 2.12/2.34              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 2.12/2.34          | ~ (v1_funct_1 @ X5)
% 2.12/2.34          | ~ (v1_relat_1 @ X5))),
% 2.12/2.34      inference('demod', [status(thm)], ['41', '42'])).
% 2.12/2.34  thf(t29_relset_1, axiom,
% 2.12/2.34    (![A:$i]:
% 2.12/2.34     ( m1_subset_1 @
% 2.12/2.34       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.12/2.34  thf('62', plain,
% 2.12/2.34      (![X13 : $i]:
% 2.12/2.34         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 2.12/2.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 2.12/2.34      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.12/2.34  thf('63', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 2.12/2.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.12/2.34  thf('64', plain,
% 2.12/2.34      (![X13 : $i]:
% 2.12/2.34         (m1_subset_1 @ (k6_partfun1 @ X13) @ 
% 2.12/2.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 2.12/2.34      inference('demod', [status(thm)], ['62', '63'])).
% 2.12/2.34  thf('65', plain,
% 2.12/2.34      (![X0 : $i]:
% 2.12/2.34         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 2.12/2.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 2.12/2.34          | ~ (v1_relat_1 @ X0)
% 2.12/2.34          | ~ (v1_funct_1 @ X0)
% 2.12/2.34          | ~ (v2_funct_1 @ X0))),
% 2.12/2.34      inference('sup+', [status(thm)], ['61', '64'])).
% 2.12/2.34  thf('66', plain,
% 2.12/2.34      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.12/2.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 2.12/2.34        | ~ (v2_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v1_relat_1 @ sk_B))),
% 2.12/2.34      inference('sup+', [status(thm)], ['60', '65'])).
% 2.12/2.34  thf('67', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['51', '56', '59'])).
% 2.12/2.34  thf('68', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('69', plain,
% 2.12/2.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.12/2.34         (~ (v1_funct_1 @ X14)
% 2.12/2.34          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 2.12/2.34          | (v2_funct_1 @ X14)
% 2.12/2.34          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_funct_2])).
% 2.12/2.34  thf('70', plain,
% 2.12/2.34      (((v2_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v1_funct_1 @ sk_B))),
% 2.12/2.34      inference('sup-', [status(thm)], ['68', '69'])).
% 2.12/2.34  thf('71', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('73', plain, ((v2_funct_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.12/2.34  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['54', '55'])).
% 2.12/2.34  thf('76', plain,
% 2.12/2.34      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.12/2.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['66', '67', '73', '74', '75'])).
% 2.12/2.34  thf(reflexivity_r2_relset_1, axiom,
% 2.12/2.34    (![A:$i,B:$i,C:$i,D:$i]:
% 2.12/2.34     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.12/2.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.12/2.34       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 2.12/2.34  thf('77', plain,
% 2.12/2.34      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.12/2.34         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 2.12/2.34          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 2.12/2.34          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 2.12/2.34      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 2.12/2.34  thf('78', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.12/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.12/2.34      inference('condensation', [status(thm)], ['77'])).
% 2.12/2.34  thf('79', plain,
% 2.12/2.34      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.12/2.34        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 2.12/2.34      inference('sup-', [status(thm)], ['76', '78'])).
% 2.12/2.34  thf('80', plain,
% 2.12/2.34      (((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 2.12/2.34         (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 2.12/2.34        | ~ (v1_relat_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v2_funct_1 @ sk_B))),
% 2.12/2.34      inference('sup+', [status(thm)], ['43', '79'])).
% 2.12/2.34  thf('81', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['51', '56', '59'])).
% 2.12/2.34  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['54', '55'])).
% 2.12/2.34  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.12/2.34  thf('85', plain,
% 2.12/2.34      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_partfun1 @ sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 2.12/2.34  thf('86', plain,
% 2.12/2.34      (((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34         (k6_partfun1 @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['40', '85'])).
% 2.12/2.34  thf('87', plain,
% 2.12/2.34      (~
% 2.12/2.34       ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.12/2.34         (k6_partfun1 @ sk_A))) | 
% 2.12/2.34       ~
% 2.12/2.34       ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.12/2.34          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.12/2.34         (k6_partfun1 @ sk_A)))),
% 2.12/2.34      inference('split', [status(esa)], ['3'])).
% 2.12/2.34  thf('88', plain,
% 2.12/2.34      (~
% 2.12/2.34       ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.12/2.34         (k6_partfun1 @ sk_A)))),
% 2.12/2.34      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 2.12/2.34  thf('89', plain,
% 2.12/2.34      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 2.12/2.34          (k6_partfun1 @ sk_A))),
% 2.12/2.34      inference('simpl_trail', [status(thm)], ['12', '88'])).
% 2.12/2.34  thf('90', plain,
% 2.12/2.34      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 2.12/2.34  thf('91', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('92', plain,
% 2.12/2.34      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.12/2.34         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.12/2.34          | ~ (v1_funct_1 @ X21)
% 2.12/2.34          | ~ (v1_funct_1 @ X24)
% 2.12/2.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.12/2.34          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 2.12/2.34              = (k5_relat_1 @ X21 @ X24)))),
% 2.12/2.34      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.12/2.34  thf('93', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 2.12/2.34            = (k5_relat_1 @ sk_B @ X0))
% 2.12/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.12/2.34          | ~ (v1_funct_1 @ X0)
% 2.12/2.34          | ~ (v1_funct_1 @ sk_B))),
% 2.12/2.34      inference('sup-', [status(thm)], ['91', '92'])).
% 2.12/2.34  thf('94', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('95', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 2.12/2.34            = (k5_relat_1 @ sk_B @ X0))
% 2.12/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.12/2.34          | ~ (v1_funct_1 @ X0))),
% 2.12/2.34      inference('demod', [status(thm)], ['93', '94'])).
% 2.12/2.34  thf('96', plain,
% 2.12/2.34      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.12/2.34        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.12/2.34            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 2.12/2.34      inference('sup-', [status(thm)], ['90', '95'])).
% 2.12/2.34  thf('97', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['30', '31'])).
% 2.12/2.34  thf('98', plain,
% 2.12/2.34      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 2.12/2.34         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 2.12/2.34      inference('demod', [status(thm)], ['96', '97'])).
% 2.12/2.34  thf('99', plain,
% 2.12/2.34      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.12/2.34          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_partfun1 @ sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['89', '98'])).
% 2.12/2.34  thf('100', plain,
% 2.12/2.34      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 2.12/2.34           (k6_partfun1 @ sk_A))
% 2.12/2.34        | ~ (v1_relat_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v2_funct_1 @ sk_B))),
% 2.12/2.34      inference('sup-', [status(thm)], ['2', '99'])).
% 2.12/2.34  thf(t55_funct_1, axiom,
% 2.12/2.34    (![A:$i]:
% 2.12/2.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.12/2.34       ( ( v2_funct_1 @ A ) =>
% 2.12/2.34         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.12/2.34           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.12/2.34  thf('101', plain,
% 2.12/2.34      (![X4 : $i]:
% 2.12/2.34         (~ (v2_funct_1 @ X4)
% 2.12/2.34          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 2.12/2.34          | ~ (v1_funct_1 @ X4)
% 2.12/2.34          | ~ (v1_relat_1 @ X4))),
% 2.12/2.34      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.12/2.34  thf('102', plain,
% 2.12/2.34      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 2.12/2.34  thf('103', plain,
% 2.12/2.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.12/2.34         (~ (v1_funct_1 @ X14)
% 2.12/2.34          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 2.12/2.34          | (v2_funct_2 @ X14 @ X16)
% 2.12/2.34          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_funct_2])).
% 2.12/2.34  thf('104', plain,
% 2.12/2.34      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 2.12/2.34        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['102', '103'])).
% 2.12/2.34  thf('105', plain,
% 2.12/2.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('106', plain,
% 2.12/2.34      (![X19 : $i, X20 : $i]:
% 2.12/2.34         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 2.12/2.34          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 2.12/2.34          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 2.12/2.34          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 2.12/2.34          | ~ (v1_funct_1 @ X20))),
% 2.12/2.34      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 2.12/2.34  thf('107', plain,
% 2.12/2.34      ((~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.12/2.34        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 2.12/2.34      inference('sup-', [status(thm)], ['105', '106'])).
% 2.12/2.34  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('109', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('110', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('111', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 2.12/2.34      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 2.12/2.34  thf('112', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.12/2.34  thf('113', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 2.12/2.34      inference('demod', [status(thm)], ['111', '112'])).
% 2.12/2.34  thf('114', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['30', '31'])).
% 2.12/2.34  thf('115', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 2.12/2.34      inference('demod', [status(thm)], ['104', '113', '114'])).
% 2.12/2.34  thf('116', plain,
% 2.12/2.34      (![X17 : $i, X18 : $i]:
% 2.12/2.34         (~ (v2_funct_2 @ X18 @ X17)
% 2.12/2.34          | ((k2_relat_1 @ X18) = (X17))
% 2.12/2.34          | ~ (v5_relat_1 @ X18 @ X17)
% 2.12/2.34          | ~ (v1_relat_1 @ X18))),
% 2.12/2.34      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.12/2.34  thf('117', plain,
% 2.12/2.34      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 2.12/2.34        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 2.12/2.34        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['115', '116'])).
% 2.12/2.34  thf('118', plain,
% 2.12/2.34      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 2.12/2.34  thf('119', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.12/2.34          | (v1_relat_1 @ X0)
% 2.12/2.34          | ~ (v1_relat_1 @ X1))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.12/2.34  thf('120', plain,
% 2.12/2.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 2.12/2.34        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.12/2.34      inference('sup-', [status(thm)], ['118', '119'])).
% 2.12/2.34  thf('121', plain,
% 2.12/2.34      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.12/2.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.12/2.34  thf('122', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['120', '121'])).
% 2.12/2.34  thf('123', plain,
% 2.12/2.34      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.12/2.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.12/2.34      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 2.12/2.34  thf('124', plain,
% 2.12/2.34      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.12/2.34         ((v5_relat_1 @ X6 @ X8)
% 2.12/2.34          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.12/2.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.12/2.34  thf('125', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 2.12/2.34      inference('sup-', [status(thm)], ['123', '124'])).
% 2.12/2.34  thf('126', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['117', '122', '125'])).
% 2.12/2.34  thf('127', plain,
% 2.12/2.34      ((((k1_relat_1 @ sk_B) = (sk_A))
% 2.12/2.34        | ~ (v1_relat_1 @ sk_B)
% 2.12/2.34        | ~ (v1_funct_1 @ sk_B)
% 2.12/2.34        | ~ (v2_funct_1 @ sk_B))),
% 2.12/2.34      inference('sup+', [status(thm)], ['101', '126'])).
% 2.12/2.34  thf('128', plain, ((v1_relat_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['54', '55'])).
% 2.12/2.34  thf('129', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('130', plain, ((v2_funct_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.12/2.34  thf('131', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 2.12/2.34      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 2.12/2.34  thf('132', plain,
% 2.12/2.34      (![X13 : $i]:
% 2.12/2.34         (m1_subset_1 @ (k6_partfun1 @ X13) @ 
% 2.12/2.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 2.12/2.34      inference('demod', [status(thm)], ['62', '63'])).
% 2.12/2.34  thf('133', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.12/2.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.12/2.34      inference('condensation', [status(thm)], ['77'])).
% 2.12/2.34  thf('134', plain,
% 2.12/2.34      (![X0 : $i]:
% 2.12/2.34         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 2.12/2.34      inference('sup-', [status(thm)], ['132', '133'])).
% 2.12/2.34  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['54', '55'])).
% 2.12/2.34  thf('136', plain, ((v1_funct_1 @ sk_B)),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf('137', plain, ((v2_funct_1 @ sk_B)),
% 2.12/2.34      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.12/2.34  thf('138', plain, ($false),
% 2.12/2.34      inference('demod', [status(thm)],
% 2.12/2.34                ['100', '131', '134', '135', '136', '137'])).
% 2.12/2.34  
% 2.12/2.34  % SZS output end Refutation
% 2.12/2.34  
% 2.12/2.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
