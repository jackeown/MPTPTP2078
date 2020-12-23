%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VdHz29dL5I

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:20 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  267 (8368 expanded)
%              Number of leaves         :   36 (2580 expanded)
%              Depth                    :   23
%              Number of atoms          : 2662 (224024 expanded)
%              Number of equality atoms :   87 (1196 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('36',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X16 @ X17 ) @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('47',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X16 @ X17 ) @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('55',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','47','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('61',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('62',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('63',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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

thf('68',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('73',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X16 @ X17 ) @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('78',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('79',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('80',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('82',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('84',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('87',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('88',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('89',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('91',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','82','91'])).

thf('93',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('95',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('96',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('98',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('99',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('103',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['70','92','93','99','100','103'])).

thf('105',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('107',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('111',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X16 @ X17 ) @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v3_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('114',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('115',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('116',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('120',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','118','119'])).

thf('121',plain,
    ( ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','120'])).

thf('122',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('125',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('129',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','125','126','132'])).

thf('134',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('135',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('140',plain,(
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
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','147'])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['133','148'])).

thf('150',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('151',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','125','126','132'])).

thf('152',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('153',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','125','126','132'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('155',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','82','91'])).

thf('156',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('157',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('158',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','125','126','132'])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('160',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('161',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('163',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('166',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('167',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['161','167'])).

thf('169',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['149','150','151','152','153','154','155','156','157','158','168'])).

thf('170',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','169'])).

thf('171',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('173',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','175'])).

thf('177',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('178',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('179',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('180',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','181'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('183',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('184',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('185',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('186',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['185','187'])).

thf('189',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['182','188'])).

thf('190',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('191',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('194',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['193','198'])).

thf('200',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('201',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('203',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('205',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('206',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('207',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('209',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207','208'])).

thf('210',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('211',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207','208'])).

thf('212',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('215',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('220',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['215','216','217','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('223',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('225',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','221','222','223','224'])).

thf('226',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['209','225'])).

thf('227',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['199','200','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['185','187'])).

thf('229',plain,(
    $false ),
    inference(demod,[status(thm)],['192','227','228'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VdHz29dL5I
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 596 iterations in 0.306s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.59/0.77  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.77  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.59/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.77  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.59/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.59/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.77  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.77  thf(t88_funct_2, conjecture,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.77       ( ( r2_relset_1 @
% 0.59/0.77           A @ A @ 
% 0.59/0.77           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.59/0.77           ( k6_partfun1 @ A ) ) & 
% 0.59/0.77         ( r2_relset_1 @
% 0.59/0.77           A @ A @ 
% 0.59/0.77           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.59/0.77           ( k6_partfun1 @ A ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i]:
% 0.59/0.77        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.77            ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.77            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.77          ( ( r2_relset_1 @
% 0.59/0.77              A @ A @ 
% 0.59/0.77              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.59/0.77              ( k6_partfun1 @ A ) ) & 
% 0.59/0.77            ( r2_relset_1 @
% 0.59/0.77              A @ A @ 
% 0.59/0.77              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.59/0.77              ( k6_partfun1 @ A ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77           (k6_partfun1 @ sk_A))
% 0.59/0.77        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77             (k6_partfun1 @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77           (k6_partfun1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf(redefinition_k6_partfun1, axiom,
% 0.59/0.77    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.59/0.77  thf('2', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77           (k6_relat_1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('demod', [status(thm)], ['1', '2'])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k2_funct_2, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.77       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X28 : $i, X29 : $i]:
% 0.59/0.77         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.59/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.59/0.77          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.77          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.77          | ~ (v1_funct_1 @ X28))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77            (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77           (k6_relat_1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('demod', [status(thm)], ['3', '10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(dt_k2_funct_2, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.77       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.59/0.77         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.77         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.77         ( m1_subset_1 @
% 0.59/0.77           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k2_funct_2 @ X16 @ X17) @ 
% 0.59/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.59/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.77  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf(redefinition_k1_partfun1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.77         ( v1_funct_1 @ F ) & 
% 0.59/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.77       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.59/0.77          | ~ (v1_funct_1 @ X22)
% 0.59/0.77          | ~ (v1_funct_1 @ X25)
% 0.59/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.59/0.77          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.59/0.77              = (k5_relat_1 @ X22 @ X25)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.59/0.77            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((v1_funct_1 @ (k2_funct_2 @ X16 @ X17))
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.77  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.59/0.77  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.59/0.77            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['22', '31'])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['12', '32'])).
% 0.59/0.77  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t65_funct_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.77       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X2 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X2)
% 0.59/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k2_funct_2 @ X16 @ X17) @ 
% 0.59/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.77  thf('39', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((v1_funct_2 @ (k2_funct_2 @ X16 @ X17) @ X16 @ X16)
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.77  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('44', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('46', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('47', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.59/0.77  thf('48', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('49', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((v3_funct_2 @ (k2_funct_2 @ X16 @ X17) @ X16 @ X16)
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.77  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('52', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('53', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('54', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('55', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.59/0.77  thf('56', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['38', '39', '47', '55'])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('58', plain,
% 0.59/0.77      (![X28 : $i, X29 : $i]:
% 0.59/0.77         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.59/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.59/0.77          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.77          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.77          | ~ (v1_funct_1 @ X28))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.59/0.77  thf('59', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.59/0.77            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['57', '58'])).
% 0.59/0.77  thf('60', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('61', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.59/0.77  thf('62', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.59/0.77  thf('63', plain,
% 0.59/0.77      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.59/0.77  thf('64', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['56', '63'])).
% 0.59/0.77  thf(cc1_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( v1_relat_1 @ C ) ))).
% 0.59/0.77  thf('65', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((v1_relat_1 @ X3)
% 0.59/0.77          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.77  thf('66', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.77  thf('67', plain,
% 0.59/0.77      (![X2 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X2)
% 0.59/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.77  thf(t61_funct_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.77       ( ( v2_funct_1 @ A ) =>
% 0.59/0.77         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.59/0.77             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.59/0.77           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.59/0.77             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.77  thf('68', plain,
% 0.59/0.77      (![X1 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X1)
% 0.59/0.77          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.59/0.77              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.77  thf('69', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.77  thf('70', plain,
% 0.59/0.77      ((~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77            (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['66', '69'])).
% 0.59/0.77  thf('71', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['56', '63'])).
% 0.59/0.77  thf(cc2_funct_2, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.59/0.77         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.59/0.77  thf('72', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (~ (v1_funct_1 @ X13)
% 0.59/0.77          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 0.59/0.77          | (v2_funct_1 @ X13)
% 0.59/0.77          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.77  thf('73', plain,
% 0.59/0.77      (((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['71', '72'])).
% 0.59/0.77  thf('74', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('75', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((v3_funct_2 @ (k2_funct_2 @ X16 @ X17) @ X16 @ X16)
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('76', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.59/0.77  thf('77', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('78', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.59/0.77  thf('79', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.59/0.77  thf('80', plain,
% 0.59/0.77      ((v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.59/0.77  thf('81', plain,
% 0.59/0.77      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.59/0.77  thf('82', plain,
% 0.59/0.77      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['80', '81'])).
% 0.59/0.77  thf('83', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('84', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((v1_funct_1 @ (k2_funct_2 @ X16 @ X17))
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('85', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['83', '84'])).
% 0.59/0.77  thf('86', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('87', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.59/0.77  thf('88', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.59/0.77  thf('89', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.59/0.77  thf('90', plain,
% 0.59/0.77      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.59/0.77  thf('91', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.59/0.77  thf('92', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['73', '82', '91'])).
% 0.59/0.77  thf('93', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.59/0.77  thf('94', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('95', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (~ (v1_funct_1 @ X13)
% 0.59/0.77          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 0.59/0.77          | (v2_funct_1 @ X13)
% 0.59/0.77          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.77  thf('96', plain,
% 0.59/0.77      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.77  thf('97', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.59/0.77  thf('98', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('99', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.59/0.77  thf('100', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('101', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('102', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((v1_relat_1 @ X3)
% 0.59/0.77          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.77  thf('103', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.59/0.77  thf('104', plain,
% 0.59/0.77      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 0.59/0.77      inference('demod', [status(thm)], ['70', '92', '93', '99', '100', '103'])).
% 0.59/0.77  thf('105', plain,
% 0.59/0.77      (![X2 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X2)
% 0.59/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.77  thf('106', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['56', '63'])).
% 0.59/0.77  thf('107', plain,
% 0.59/0.77      (![X28 : $i, X29 : $i]:
% 0.59/0.77         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.59/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.59/0.77          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.77          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.77          | ~ (v1_funct_1 @ X28))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.59/0.77  thf('108', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.59/0.77        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['106', '107'])).
% 0.59/0.77  thf('109', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.59/0.77  thf('110', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('111', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]:
% 0.59/0.77         ((v1_funct_2 @ (k2_funct_2 @ X16 @ X17) @ X16 @ X16)
% 0.59/0.77          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.59/0.77          | ~ (v3_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_2 @ X17 @ X16 @ X16)
% 0.59/0.77          | ~ (v1_funct_1 @ X17))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.77  thf('112', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['110', '111'])).
% 0.59/0.77  thf('113', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('114', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.59/0.77  thf('115', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.59/0.77  thf('116', plain,
% 0.59/0.77      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.59/0.77  thf('117', plain,
% 0.59/0.77      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.59/0.77  thf('118', plain,
% 0.59/0.77      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['116', '117'])).
% 0.59/0.77  thf('119', plain,
% 0.59/0.77      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['80', '81'])).
% 0.59/0.77  thf('120', plain,
% 0.59/0.77      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['108', '109', '118', '119'])).
% 0.59/0.77  thf('121', plain,
% 0.59/0.77      ((((k2_funct_2 @ sk_A @ sk_B)
% 0.59/0.77          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v2_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup+', [status(thm)], ['105', '120'])).
% 0.59/0.77  thf('122', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('123', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('124', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((v1_relat_1 @ X3)
% 0.59/0.77          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.77  thf('125', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.77      inference('sup-', [status(thm)], ['123', '124'])).
% 0.59/0.77  thf('126', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('127', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('128', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (~ (v1_funct_1 @ X13)
% 0.59/0.77          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 0.59/0.77          | (v2_funct_1 @ X13)
% 0.59/0.77          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.77  thf('129', plain,
% 0.59/0.77      (((v2_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['127', '128'])).
% 0.59/0.77  thf('130', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('131', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('132', plain, ((v2_funct_1 @ sk_B)),
% 0.59/0.77      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.59/0.77  thf('133', plain,
% 0.59/0.77      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['121', '122', '125', '126', '132'])).
% 0.59/0.77  thf('134', plain,
% 0.59/0.77      (![X2 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X2)
% 0.59/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.77  thf('135', plain,
% 0.59/0.77      (![X1 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X1)
% 0.59/0.77          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.59/0.77              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.77  thf(fc6_funct_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.59/0.77       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.59/0.77         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.59/0.77         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.59/0.77  thf('136', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.77  thf('137', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.77  thf('138', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.59/0.77  thf('139', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.77  thf('140', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['138', '139'])).
% 0.59/0.77  thf('141', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['140'])).
% 0.59/0.77  thf('142', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['137', '141'])).
% 0.59/0.77  thf('143', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['142'])).
% 0.59/0.77  thf('144', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['136', '143'])).
% 0.59/0.77  thf('145', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['144'])).
% 0.59/0.77  thf('146', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['135', '145'])).
% 0.59/0.77  thf('147', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.59/0.77              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['146'])).
% 0.59/0.77  thf('148', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['134', '147'])).
% 0.59/0.77  thf('149', plain,
% 0.59/0.77      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))
% 0.59/0.77        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77        | ((k6_relat_1 @ 
% 0.59/0.77            (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['133', '148'])).
% 0.59/0.77  thf('150', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.59/0.77  thf('151', plain,
% 0.59/0.77      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['121', '122', '125', '126', '132'])).
% 0.59/0.77  thf('152', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.59/0.77  thf('153', plain,
% 0.59/0.77      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['121', '122', '125', '126', '132'])).
% 0.59/0.77  thf('154', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('155', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['73', '82', '91'])).
% 0.59/0.77  thf('156', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.59/0.77  thf('157', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.77  thf('158', plain,
% 0.59/0.77      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['121', '122', '125', '126', '132'])).
% 0.59/0.77  thf('159', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.77  thf('160', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.77         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.59/0.77          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.77  thf('161', plain,
% 0.59/0.77      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['159', '160'])).
% 0.59/0.77  thf('162', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf(t67_funct_2, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.77       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.59/0.77  thf('163', plain,
% 0.59/0.77      (![X31 : $i, X32 : $i]:
% 0.59/0.77         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.59/0.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.77          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.77          | ~ (v1_funct_1 @ X32))),
% 0.59/0.77      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.59/0.77  thf('164', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.59/0.77        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['162', '163'])).
% 0.59/0.77  thf('165', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('166', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.59/0.77  thf('167', plain,
% 0.59/0.77      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.59/0.77  thf('168', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['161', '167'])).
% 0.59/0.77  thf('169', plain,
% 0.59/0.77      (((k6_relat_1 @ sk_A)
% 0.59/0.77         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 0.59/0.77      inference('demod', [status(thm)],
% 0.59/0.77                ['149', '150', '151', '152', '153', '154', '155', '156', 
% 0.59/0.77                 '157', '158', '168'])).
% 0.59/0.77  thf('170', plain,
% 0.59/0.77      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.59/0.77         = (k6_relat_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['104', '169'])).
% 0.59/0.77  thf('171', plain,
% 0.59/0.77      ((((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v2_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup+', [status(thm)], ['35', '170'])).
% 0.59/0.77  thf('172', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.77      inference('sup-', [status(thm)], ['123', '124'])).
% 0.59/0.77  thf('173', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('174', plain, ((v2_funct_1 @ sk_B)),
% 0.59/0.77      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.59/0.77  thf('175', plain,
% 0.59/0.77      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 0.59/0.77  thf('176', plain,
% 0.59/0.77      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.59/0.77         = (k6_relat_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['33', '34', '175'])).
% 0.59/0.77  thf('177', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.77  thf('178', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77           (k6_partfun1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('179', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.77  thf('180', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77           (k6_relat_1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('demod', [status(thm)], ['178', '179'])).
% 0.59/0.77  thf('181', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77            sk_B) @ 
% 0.59/0.77           (k6_relat_1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['177', '180'])).
% 0.59/0.77  thf('182', plain,
% 0.59/0.77      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.59/0.77           (k6_relat_1 @ sk_A)))
% 0.59/0.77         <= (~
% 0.59/0.77             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77               (k6_partfun1 @ sk_A))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['176', '181'])).
% 0.59/0.77  thf(dt_k6_partfun1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( m1_subset_1 @
% 0.59/0.77         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.59/0.77       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.59/0.77  thf('183', plain,
% 0.59/0.77      (![X19 : $i]:
% 0.59/0.77         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.59/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.59/0.77  thf('184', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.77  thf('185', plain,
% 0.59/0.77      (![X19 : $i]:
% 0.59/0.77         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.59/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.59/0.77      inference('demod', [status(thm)], ['183', '184'])).
% 0.59/0.77  thf(reflexivity_r2_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.77       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.59/0.77  thf('186', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.77         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 0.59/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.59/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.59/0.77      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.59/0.77  thf('187', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.59/0.77      inference('condensation', [status(thm)], ['186'])).
% 0.59/0.77  thf('188', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['185', '187'])).
% 0.59/0.77  thf('189', plain,
% 0.59/0.77      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77         (k6_partfun1 @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['182', '188'])).
% 0.59/0.77  thf('190', plain,
% 0.59/0.77      (~
% 0.59/0.77       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77         (k6_partfun1 @ sk_A))) | 
% 0.59/0.77       ~
% 0.59/0.77       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.77          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.59/0.77         (k6_partfun1 @ sk_A)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('191', plain,
% 0.59/0.77      (~
% 0.59/0.77       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.59/0.77         (k6_partfun1 @ sk_A)))),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['189', '190'])).
% 0.59/0.77  thf('192', plain,
% 0.59/0.77      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.77          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.59/0.77          (k6_relat_1 @ sk_A))),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['11', '191'])).
% 0.59/0.77  thf('193', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.59/0.77  thf('194', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('195', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.59/0.77          | ~ (v1_funct_1 @ X22)
% 0.59/0.77          | ~ (v1_funct_1 @ X25)
% 0.59/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.59/0.77          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.59/0.77              = (k5_relat_1 @ X22 @ X25)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.59/0.77  thf('196', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.59/0.77            = (k5_relat_1 @ sk_B @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['194', '195'])).
% 0.59/0.77  thf('197', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('198', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.59/0.77            = (k5_relat_1 @ sk_B @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['196', '197'])).
% 0.59/0.77  thf('199', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.59/0.77            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['193', '198'])).
% 0.59/0.77  thf('200', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('201', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.59/0.77  thf('202', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | ~ (v2_funct_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.77  thf('203', plain,
% 0.59/0.77      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.59/0.77        | ~ (v2_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.77        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.59/0.77            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['201', '202'])).
% 0.59/0.77  thf('204', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.59/0.77  thf('205', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('206', plain, ((v2_funct_1 @ sk_B)),
% 0.59/0.77      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.59/0.77  thf('207', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('208', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.77      inference('sup-', [status(thm)], ['123', '124'])).
% 0.59/0.77  thf('209', plain,
% 0.59/0.77      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)],
% 0.59/0.77                ['203', '204', '205', '206', '207', '208'])).
% 0.59/0.77  thf('210', plain,
% 0.59/0.77      (![X1 : $i]:
% 0.59/0.77         (~ (v2_funct_1 @ X1)
% 0.59/0.77          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.59/0.77              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.59/0.77          | ~ (v1_funct_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.77  thf('211', plain,
% 0.59/0.77      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)],
% 0.59/0.77                ['203', '204', '205', '206', '207', '208'])).
% 0.59/0.77  thf('212', plain,
% 0.59/0.77      ((((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.59/0.77          = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v2_funct_1 @ sk_B))),
% 0.59/0.77      inference('sup+', [status(thm)], ['210', '211'])).
% 0.59/0.77  thf('213', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('214', plain,
% 0.59/0.77      (![X31 : $i, X32 : $i]:
% 0.59/0.77         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.59/0.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.77          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.77          | ~ (v1_funct_1 @ X32))),
% 0.59/0.77      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.59/0.77  thf('215', plain,
% 0.59/0.77      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.77        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['213', '214'])).
% 0.59/0.77  thf('216', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('217', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('218', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('219', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.77         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.59/0.77          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.77  thf('220', plain,
% 0.59/0.77      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['218', '219'])).
% 0.59/0.77  thf('221', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['215', '216', '217', '220'])).
% 0.59/0.77  thf('222', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.77      inference('sup-', [status(thm)], ['123', '124'])).
% 0.59/0.77  thf('223', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('224', plain, ((v2_funct_1 @ sk_B)),
% 0.59/0.77      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.59/0.77  thf('225', plain,
% 0.59/0.77      (((k6_relat_1 @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['212', '221', '222', '223', '224'])).
% 0.59/0.77  thf('226', plain,
% 0.59/0.77      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['209', '225'])).
% 0.59/0.77  thf('227', plain,
% 0.59/0.77      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.59/0.77         = (k6_relat_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['199', '200', '226'])).
% 0.59/0.77  thf('228', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['185', '187'])).
% 0.59/0.77  thf('229', plain, ($false),
% 0.59/0.77      inference('demod', [status(thm)], ['192', '227', '228'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
