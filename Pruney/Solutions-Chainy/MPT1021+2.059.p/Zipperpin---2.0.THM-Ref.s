%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.17mkXd16qs

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:20 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 854 expanded)
%              Number of leaves         :   35 ( 273 expanded)
%              Depth                    :   15
%              Number of atoms          : 1889 (21107 expanded)
%              Number of equality atoms :   65 ( 159 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ( ( k2_funct_2 @ X27 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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

thf('17',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
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
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('52',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('54',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('71',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X29 @ X30 )
        = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['72','73','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['69','82'])).

thf('84',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','84'])).

thf('86',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('90',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('91',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('93',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','95'])).

thf('97',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('108',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X2 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('109',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('110',plain,(
    ! [X1: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('111',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('112',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('113',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('114',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('115',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('127',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('129',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('130',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('131',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('133',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('134',plain,
    ( ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['124','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X29 @ X30 )
        = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('142',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['137','138','139','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('145',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('147',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['134','143','144','145','146'])).

thf('148',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['99','148','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.17mkXd16qs
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.88  % Solved by: fo/fo7.sh
% 0.72/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.88  % done 609 iterations in 0.425s
% 0.72/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.88  % SZS output start Refutation
% 0.72/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.72/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.72/0.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.72/0.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.72/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.72/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.72/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.72/0.88  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.72/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.88  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.72/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.72/0.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.72/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.88  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.72/0.88  thf(t88_funct_2, conjecture,
% 0.72/0.88    (![A:$i,B:$i]:
% 0.72/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.72/0.88         ( v3_funct_2 @ B @ A @ A ) & 
% 0.72/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.72/0.88       ( ( r2_relset_1 @
% 0.72/0.88           A @ A @ 
% 0.72/0.88           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.72/0.88           ( k6_partfun1 @ A ) ) & 
% 0.72/0.88         ( r2_relset_1 @
% 0.72/0.88           A @ A @ 
% 0.72/0.88           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.72/0.88           ( k6_partfun1 @ A ) ) ) ))).
% 0.72/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.88    (~( ![A:$i,B:$i]:
% 0.72/0.88        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.72/0.88            ( v3_funct_2 @ B @ A @ A ) & 
% 0.72/0.88            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.72/0.88          ( ( r2_relset_1 @
% 0.72/0.88              A @ A @ 
% 0.72/0.88              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.72/0.88              ( k6_partfun1 @ A ) ) & 
% 0.72/0.88            ( r2_relset_1 @
% 0.72/0.88              A @ A @ 
% 0.72/0.88              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.72/0.88              ( k6_partfun1 @ A ) ) ) ) )),
% 0.72/0.88    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.72/0.88  thf('0', plain,
% 0.72/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.88            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.72/0.88           (k6_partfun1 @ sk_A))
% 0.72/0.88        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.88             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.88              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.88             (k6_partfun1 @ sk_A)))),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('1', plain,
% 0.72/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.88            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.72/0.88           (k6_partfun1 @ sk_A)))
% 0.72/0.88         <= (~
% 0.72/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.88                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.72/0.88               (k6_partfun1 @ sk_A))))),
% 0.72/0.88      inference('split', [status(esa)], ['0'])).
% 0.72/0.88  thf('2', plain,
% 0.72/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf(redefinition_k2_funct_2, axiom,
% 0.72/0.88    (![A:$i,B:$i]:
% 0.72/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.72/0.88         ( v3_funct_2 @ B @ A @ A ) & 
% 0.72/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.72/0.88       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.72/0.88  thf('3', plain,
% 0.72/0.88      (![X26 : $i, X27 : $i]:
% 0.72/0.88         (((k2_funct_2 @ X27 @ X26) = (k2_funct_1 @ X26))
% 0.72/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 0.72/0.88          | ~ (v3_funct_2 @ X26 @ X27 @ X27)
% 0.72/0.88          | ~ (v1_funct_2 @ X26 @ X27 @ X27)
% 0.72/0.88          | ~ (v1_funct_1 @ X26))),
% 0.72/0.88      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.72/0.88  thf('4', plain,
% 0.72/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.88        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.72/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.72/0.88  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('6', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('7', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.72/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.72/0.88  thf('9', plain,
% 0.72/0.88      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.88           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.88            (k2_funct_1 @ sk_B_1)) @ 
% 0.72/0.88           (k6_partfun1 @ sk_A)))
% 0.72/0.88         <= (~
% 0.72/0.88             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.88               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.88                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.72/0.88               (k6_partfun1 @ sk_A))))),
% 0.72/0.88      inference('demod', [status(thm)], ['1', '8'])).
% 0.72/0.88  thf('10', plain,
% 0.72/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('11', plain,
% 0.72/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf(dt_k2_funct_2, axiom,
% 0.72/0.88    (![A:$i,B:$i]:
% 0.72/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.72/0.88         ( v3_funct_2 @ B @ A @ A ) & 
% 0.72/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.72/0.88       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.72/0.88         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.72/0.88         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.72/0.88         ( m1_subset_1 @
% 0.72/0.88           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.72/0.88  thf('12', plain,
% 0.72/0.88      (![X18 : $i, X19 : $i]:
% 0.72/0.88         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.72/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.72/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.72/0.88          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.88          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.88          | ~ (v1_funct_1 @ X19))),
% 0.72/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.72/0.88  thf('13', plain,
% 0.72/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.88        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.72/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.72/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.72/0.88  thf('14', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('15', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('16', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.72/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.72/0.88  thf('18', plain,
% 0.72/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.88      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.72/0.88  thf(redefinition_k1_partfun1, axiom,
% 0.72/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.72/0.88     ( ( ( v1_funct_1 @ E ) & 
% 0.72/0.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.72/0.88         ( v1_funct_1 @ F ) & 
% 0.72/0.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.72/0.88       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.72/0.88  thf('19', plain,
% 0.72/0.88      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.72/0.88         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.72/0.88          | ~ (v1_funct_1 @ X20)
% 0.72/0.88          | ~ (v1_funct_1 @ X23)
% 0.72/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.72/0.88          | ((k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 0.72/0.88              = (k5_relat_1 @ X20 @ X23)))),
% 0.72/0.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.72/0.88  thf('20', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.88         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.72/0.88            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.72/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.72/0.88          | ~ (v1_funct_1 @ X0)
% 0.72/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.72/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.72/0.88  thf('21', plain,
% 0.72/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('22', plain,
% 0.72/0.88      (![X18 : $i, X19 : $i]:
% 0.72/0.88         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.72/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.72/0.88          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.88          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.88          | ~ (v1_funct_1 @ X19))),
% 0.72/0.88      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.72/0.88  thf('23', plain,
% 0.72/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.88        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.88        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.88        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.72/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.72/0.88  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('25', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('26', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('27', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.72/0.88      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.72/0.88  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.72/0.88      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.72/0.88  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.88      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.88  thf('30', plain,
% 0.72/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.88         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.72/0.88            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.72/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.72/0.88          | ~ (v1_funct_1 @ X0))),
% 0.72/0.88      inference('demod', [status(thm)], ['20', '29'])).
% 0.72/0.88  thf('31', plain,
% 0.72/0.88      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.88        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.88            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.72/0.88      inference('sup-', [status(thm)], ['10', '30'])).
% 0.72/0.88  thf('32', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.88  thf('33', plain,
% 0.72/0.88      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.88      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.72/0.88  thf(cc1_relset_1, axiom,
% 0.72/0.88    (![A:$i,B:$i,C:$i]:
% 0.72/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.88       ( v1_relat_1 @ C ) ))).
% 0.72/0.88  thf('34', plain,
% 0.72/0.88      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.72/0.88         ((v1_relat_1 @ X4)
% 0.72/0.88          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.72/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.88  thf('35', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.88  thf(t65_funct_1, axiom,
% 0.72/0.88    (![A:$i]:
% 0.72/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.72/0.88       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.72/0.88  thf('36', plain,
% 0.72/0.88      (![X3 : $i]:
% 0.72/0.88         (~ (v2_funct_1 @ X3)
% 0.72/0.88          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.72/0.88          | ~ (v1_funct_1 @ X3)
% 0.72/0.88          | ~ (v1_relat_1 @ X3))),
% 0.72/0.88      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.72/0.88  thf(t61_funct_1, axiom,
% 0.72/0.88    (![A:$i]:
% 0.72/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.72/0.88       ( ( v2_funct_1 @ A ) =>
% 0.72/0.88         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.72/0.88             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.72/0.88           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.72/0.88             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.72/0.88  thf('37', plain,
% 0.72/0.88      (![X2 : $i]:
% 0.72/0.88         (~ (v2_funct_1 @ X2)
% 0.72/0.88          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 0.72/0.88              = (k6_relat_1 @ (k1_relat_1 @ X2)))
% 0.72/0.89          | ~ (v1_funct_1 @ X2)
% 0.72/0.89          | ~ (v1_relat_1 @ X2))),
% 0.72/0.89      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.72/0.89  thf(redefinition_k6_partfun1, axiom,
% 0.72/0.89    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.72/0.89  thf('38', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.89  thf('39', plain,
% 0.72/0.89      (![X2 : $i]:
% 0.72/0.89         (~ (v2_funct_1 @ X2)
% 0.72/0.89          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 0.72/0.89              = (k6_partfun1 @ (k1_relat_1 @ X2)))
% 0.72/0.89          | ~ (v1_funct_1 @ X2)
% 0.72/0.89          | ~ (v1_relat_1 @ X2))),
% 0.72/0.89      inference('demod', [status(thm)], ['37', '38'])).
% 0.72/0.89  thf('40', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.72/0.89            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.72/0.89      inference('sup+', [status(thm)], ['36', '39'])).
% 0.72/0.89  thf('41', plain,
% 0.72/0.89      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ~ (v2_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_relat_1 @ sk_B_1)
% 0.72/0.89        | ((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)
% 0.72/0.89            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['35', '40'])).
% 0.72/0.89  thf('42', plain,
% 0.72/0.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.72/0.89  thf(cc2_funct_2, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.89       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.72/0.89         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.72/0.89  thf('43', plain,
% 0.72/0.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.89         (~ (v1_funct_1 @ X15)
% 0.72/0.89          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.72/0.89          | (v2_funct_1 @ X15)
% 0.72/0.89          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.72/0.89      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.72/0.89  thf('44', plain,
% 0.72/0.89      (((v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.72/0.89        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.72/0.89  thf('45', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('46', plain,
% 0.72/0.89      (![X18 : $i, X19 : $i]:
% 0.72/0.89         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.72/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.72/0.89          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.89          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.89          | ~ (v1_funct_1 @ X19))),
% 0.72/0.89      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.72/0.89  thf('47', plain,
% 0.72/0.89      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.89        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.89        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.72/0.89      inference('sup-', [status(thm)], ['45', '46'])).
% 0.72/0.89  thf('48', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('49', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('50', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.72/0.89  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.72/0.89      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.72/0.89  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.89  thf('54', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.72/0.89  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.89  thf('56', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('57', plain,
% 0.72/0.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.89         (~ (v1_funct_1 @ X15)
% 0.72/0.89          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.72/0.89          | (v2_funct_1 @ X15)
% 0.72/0.89          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.72/0.89      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.72/0.89  thf('58', plain,
% 0.72/0.89      (((v2_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.89        | ~ (v1_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.72/0.89  thf('59', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('60', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('61', plain, ((v2_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.72/0.89  thf('62', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('63', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('64', plain,
% 0.72/0.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.72/0.89         ((v1_relat_1 @ X4)
% 0.72/0.89          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.72/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.89  thf('65', plain, ((v1_relat_1 @ sk_B_1)),
% 0.72/0.89      inference('sup-', [status(thm)], ['63', '64'])).
% 0.72/0.89  thf('66', plain,
% 0.72/0.89      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)
% 0.72/0.89         = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.72/0.89      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '65'])).
% 0.72/0.89  thf('67', plain,
% 0.72/0.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.72/0.89  thf(redefinition_k1_relset_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.72/0.89  thf('68', plain,
% 0.72/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.72/0.89         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.72/0.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.72/0.89  thf('69', plain,
% 0.72/0.89      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89         = (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['67', '68'])).
% 0.72/0.89  thf('70', plain,
% 0.72/0.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.72/0.89  thf(t67_funct_2, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.72/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.72/0.89       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.72/0.89  thf('71', plain,
% 0.72/0.89      (![X29 : $i, X30 : $i]:
% 0.72/0.89         (((k1_relset_1 @ X29 @ X29 @ X30) = (X29))
% 0.72/0.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.72/0.89          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.72/0.89          | ~ (v1_funct_1 @ X30))),
% 0.72/0.89      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.72/0.89  thf('72', plain,
% 0.72/0.89      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.72/0.89        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['70', '71'])).
% 0.72/0.89  thf('73', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.89  thf('74', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('75', plain,
% 0.72/0.89      (![X18 : $i, X19 : $i]:
% 0.72/0.89         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.72/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.72/0.89          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.89          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.72/0.89          | ~ (v1_funct_1 @ X19))),
% 0.72/0.89      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.72/0.89  thf('76', plain,
% 0.72/0.89      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.89        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.89        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.72/0.89      inference('sup-', [status(thm)], ['74', '75'])).
% 0.72/0.89  thf('77', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('78', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('79', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('80', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.72/0.89  thf('81', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.72/0.89      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.72/0.89  thf('82', plain,
% 0.72/0.89      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.72/0.89      inference('demod', [status(thm)], ['72', '73', '81'])).
% 0.72/0.89  thf('83', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.72/0.89      inference('sup+', [status(thm)], ['69', '82'])).
% 0.72/0.89  thf('84', plain,
% 0.72/0.89      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.72/0.89      inference('demod', [status(thm)], ['66', '83'])).
% 0.72/0.89  thf('85', plain,
% 0.72/0.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.89         sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.72/0.89      inference('demod', [status(thm)], ['31', '32', '84'])).
% 0.72/0.89  thf('86', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.72/0.89  thf('87', plain,
% 0.72/0.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.89            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.89           (k6_partfun1 @ sk_A)))
% 0.72/0.89         <= (~
% 0.72/0.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.89                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.89               (k6_partfun1 @ sk_A))))),
% 0.72/0.89      inference('split', [status(esa)], ['0'])).
% 0.72/0.89  thf('88', plain,
% 0.72/0.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.89            sk_B_1) @ 
% 0.72/0.89           (k6_partfun1 @ sk_A)))
% 0.72/0.89         <= (~
% 0.72/0.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.89                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.89               (k6_partfun1 @ sk_A))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['86', '87'])).
% 0.72/0.89  thf('89', plain,
% 0.72/0.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.72/0.89           (k6_partfun1 @ sk_A)))
% 0.72/0.89         <= (~
% 0.72/0.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.89                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.89               (k6_partfun1 @ sk_A))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['85', '88'])).
% 0.72/0.89  thf(t29_relset_1, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( m1_subset_1 @
% 0.72/0.89       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.72/0.89  thf('90', plain,
% 0.72/0.89      (![X14 : $i]:
% 0.72/0.89         (m1_subset_1 @ (k6_relat_1 @ X14) @ 
% 0.72/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.72/0.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.72/0.89  thf('91', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.89  thf('92', plain,
% 0.72/0.89      (![X14 : $i]:
% 0.72/0.89         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 0.72/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.72/0.89      inference('demod', [status(thm)], ['90', '91'])).
% 0.72/0.89  thf(reflexivity_r2_relset_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.89     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.72/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.89       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.72/0.89  thf('93', plain,
% 0.72/0.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.72/0.89         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.72/0.89          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.72/0.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.72/0.89      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.72/0.89  thf('94', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.72/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.72/0.89      inference('condensation', [status(thm)], ['93'])).
% 0.72/0.89  thf('95', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['92', '94'])).
% 0.72/0.89  thf('96', plain,
% 0.72/0.89      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.89          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.89         (k6_partfun1 @ sk_A)))),
% 0.72/0.89      inference('demod', [status(thm)], ['89', '95'])).
% 0.72/0.89  thf('97', plain,
% 0.72/0.89      (~
% 0.72/0.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.89          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.72/0.89         (k6_partfun1 @ sk_A))) | 
% 0.72/0.89       ~
% 0.72/0.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.72/0.89          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.72/0.89         (k6_partfun1 @ sk_A)))),
% 0.72/0.89      inference('split', [status(esa)], ['0'])).
% 0.72/0.89  thf('98', plain,
% 0.72/0.89      (~
% 0.72/0.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.89          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.72/0.89         (k6_partfun1 @ sk_A)))),
% 0.72/0.89      inference('sat_resolution*', [status(thm)], ['96', '97'])).
% 0.72/0.89  thf('99', plain,
% 0.72/0.89      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.89          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.89           (k2_funct_1 @ sk_B_1)) @ 
% 0.72/0.89          (k6_partfun1 @ sk_A))),
% 0.72/0.89      inference('simpl_trail', [status(thm)], ['9', '98'])).
% 0.72/0.89  thf('100', plain,
% 0.72/0.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.72/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.72/0.89  thf('101', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('102', plain,
% 0.72/0.89      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.72/0.89         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.72/0.89          | ~ (v1_funct_1 @ X20)
% 0.72/0.89          | ~ (v1_funct_1 @ X23)
% 0.72/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.72/0.89          | ((k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 0.72/0.89              = (k5_relat_1 @ X20 @ X23)))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.72/0.89  thf('103', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.72/0.89            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.72/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['101', '102'])).
% 0.72/0.89  thf('104', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('105', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.72/0.89            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.72/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.72/0.89          | ~ (v1_funct_1 @ X0))),
% 0.72/0.89      inference('demod', [status(thm)], ['103', '104'])).
% 0.72/0.89  thf('106', plain,
% 0.72/0.89      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.89            (k2_funct_1 @ sk_B_1))
% 0.72/0.89            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['100', '105'])).
% 0.72/0.89  thf('107', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.89  thf('108', plain,
% 0.72/0.89      (![X2 : $i]:
% 0.72/0.89         (~ (v2_funct_1 @ X2)
% 0.72/0.89          | ((k5_relat_1 @ X2 @ (k2_funct_1 @ X2))
% 0.72/0.89              = (k6_partfun1 @ (k1_relat_1 @ X2)))
% 0.72/0.89          | ~ (v1_funct_1 @ X2)
% 0.72/0.89          | ~ (v1_relat_1 @ X2))),
% 0.72/0.89      inference('demod', [status(thm)], ['37', '38'])).
% 0.72/0.89  thf(fc6_funct_1, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.72/0.89       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.72/0.89         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.72/0.89         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.72/0.89  thf('109', plain,
% 0.72/0.89      (![X1 : $i]:
% 0.72/0.89         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.72/0.89          | ~ (v2_funct_1 @ X1)
% 0.72/0.89          | ~ (v1_funct_1 @ X1)
% 0.72/0.89          | ~ (v1_relat_1 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.72/0.89  thf('110', plain,
% 0.72/0.89      (![X1 : $i]:
% 0.72/0.89         ((v1_funct_1 @ (k2_funct_1 @ X1))
% 0.72/0.89          | ~ (v2_funct_1 @ X1)
% 0.72/0.89          | ~ (v1_funct_1 @ X1)
% 0.72/0.89          | ~ (v1_relat_1 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.72/0.89  thf('111', plain,
% 0.72/0.89      (![X1 : $i]:
% 0.72/0.89         ((v1_relat_1 @ (k2_funct_1 @ X1))
% 0.72/0.89          | ~ (v2_funct_1 @ X1)
% 0.72/0.89          | ~ (v1_funct_1 @ X1)
% 0.72/0.89          | ~ (v1_relat_1 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.72/0.89  thf('112', plain,
% 0.72/0.89      (![X3 : $i]:
% 0.72/0.89         (~ (v2_funct_1 @ X3)
% 0.72/0.89          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.72/0.89          | ~ (v1_funct_1 @ X3)
% 0.72/0.89          | ~ (v1_relat_1 @ X3))),
% 0.72/0.89      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.72/0.89  thf('113', plain,
% 0.72/0.89      (![X2 : $i]:
% 0.72/0.89         (~ (v2_funct_1 @ X2)
% 0.72/0.89          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.72/0.89              = (k6_relat_1 @ (k2_relat_1 @ X2)))
% 0.72/0.89          | ~ (v1_funct_1 @ X2)
% 0.72/0.89          | ~ (v1_relat_1 @ X2))),
% 0.72/0.89      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.72/0.89  thf('114', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.89  thf('115', plain,
% 0.72/0.89      (![X2 : $i]:
% 0.72/0.89         (~ (v2_funct_1 @ X2)
% 0.72/0.89          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.72/0.89              = (k6_partfun1 @ (k2_relat_1 @ X2)))
% 0.72/0.89          | ~ (v1_funct_1 @ X2)
% 0.72/0.89          | ~ (v1_relat_1 @ X2))),
% 0.72/0.89      inference('demod', [status(thm)], ['113', '114'])).
% 0.72/0.89  thf('116', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.72/0.89      inference('sup+', [status(thm)], ['112', '115'])).
% 0.72/0.89  thf('117', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['111', '116'])).
% 0.72/0.89  thf('118', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0))),
% 0.72/0.89      inference('simplify', [status(thm)], ['117'])).
% 0.72/0.89  thf('119', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['110', '118'])).
% 0.72/0.89  thf('120', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0))),
% 0.72/0.89      inference('simplify', [status(thm)], ['119'])).
% 0.72/0.89  thf('121', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['109', '120'])).
% 0.72/0.89  thf('122', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0))),
% 0.72/0.89      inference('simplify', [status(thm)], ['121'])).
% 0.72/0.89  thf('123', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0))),
% 0.72/0.89      inference('sup+', [status(thm)], ['108', '122'])).
% 0.72/0.89  thf('124', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.72/0.89              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.72/0.89      inference('simplify', [status(thm)], ['123'])).
% 0.72/0.89  thf('125', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.89  thf('126', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.72/0.89          | ~ (v1_relat_1 @ X0)
% 0.72/0.89          | ~ (v1_funct_1 @ X0)
% 0.72/0.89          | ~ (v2_funct_1 @ X0)
% 0.72/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.72/0.89          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.72/0.89      inference('sup+', [status(thm)], ['112', '115'])).
% 0.72/0.89  thf('127', plain,
% 0.72/0.89      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89        | ~ (v2_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_relat_1 @ sk_B_1)
% 0.72/0.89        | ((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.72/0.89      inference('sup-', [status(thm)], ['125', '126'])).
% 0.72/0.89  thf('128', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.72/0.89  thf('129', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.89  thf('130', plain, ((v2_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.72/0.89  thf('131', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('132', plain, ((v1_relat_1 @ sk_B_1)),
% 0.72/0.89      inference('sup-', [status(thm)], ['63', '64'])).
% 0.72/0.89  thf('133', plain,
% 0.72/0.89      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.72/0.89      inference('demod', [status(thm)],
% 0.72/0.89                ['127', '128', '129', '130', '131', '132'])).
% 0.72/0.89  thf('134', plain,
% 0.72/0.89      ((((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.72/0.89          = (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 0.72/0.89        | ~ (v1_relat_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v2_funct_1 @ sk_B_1))),
% 0.72/0.89      inference('sup+', [status(thm)], ['124', '133'])).
% 0.72/0.89  thf('135', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('136', plain,
% 0.72/0.89      (![X29 : $i, X30 : $i]:
% 0.72/0.89         (((k1_relset_1 @ X29 @ X29 @ X30) = (X29))
% 0.72/0.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.72/0.89          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.72/0.89          | ~ (v1_funct_1 @ X30))),
% 0.72/0.89      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.72/0.89  thf('137', plain,
% 0.72/0.89      ((~ (v1_funct_1 @ sk_B_1)
% 0.72/0.89        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.72/0.89        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['135', '136'])).
% 0.72/0.89  thf('138', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('139', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('140', plain,
% 0.72/0.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('141', plain,
% 0.72/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.72/0.89         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.72/0.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.72/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.72/0.89  thf('142', plain,
% 0.72/0.89      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['140', '141'])).
% 0.72/0.89  thf('143', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.72/0.89      inference('demod', [status(thm)], ['137', '138', '139', '142'])).
% 0.72/0.89  thf('144', plain, ((v1_relat_1 @ sk_B_1)),
% 0.72/0.89      inference('sup-', [status(thm)], ['63', '64'])).
% 0.72/0.89  thf('145', plain, ((v1_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('146', plain, ((v2_funct_1 @ sk_B_1)),
% 0.72/0.89      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.72/0.89  thf('147', plain,
% 0.72/0.89      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) = (k6_partfun1 @ sk_A))),
% 0.72/0.89      inference('demod', [status(thm)], ['134', '143', '144', '145', '146'])).
% 0.72/0.89  thf('148', plain,
% 0.72/0.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.72/0.89         (k2_funct_1 @ sk_B_1)) = (k6_partfun1 @ sk_A))),
% 0.72/0.89      inference('demod', [status(thm)], ['106', '107', '147'])).
% 0.72/0.89  thf('149', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['92', '94'])).
% 0.72/0.89  thf('150', plain, ($false),
% 0.72/0.89      inference('demod', [status(thm)], ['99', '148', '149'])).
% 0.72/0.89  
% 0.72/0.89  % SZS output end Refutation
% 0.72/0.89  
% 0.72/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
