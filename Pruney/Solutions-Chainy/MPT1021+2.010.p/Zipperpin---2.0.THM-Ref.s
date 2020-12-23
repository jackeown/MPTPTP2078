%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZKdq08vJBd

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:11 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  268 (9091 expanded)
%              Number of leaves         :   37 (2802 expanded)
%              Depth                    :   22
%              Number of atoms          : 2734 (243247 expanded)
%              Number of equality atoms :   89 (1301 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('33',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('34',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X22 @ X23 ) @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('46',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X22 @ X23 ) @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('54',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','46','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('60',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('61',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('62',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('70',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('71',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('72',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('74',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('76',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X22 @ X23 ) @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('79',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('80',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('83',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X22 @ X23 ) @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('88',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('89',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('90',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('92',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['65','74','83','92'])).

thf('94',plain,
    ( ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['34','93'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('100',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
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

thf('103',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('104',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','100','101','107'])).

thf('109',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf('110',plain,(
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

thf('111',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('112',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('116',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('117',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','100','101','107'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('120',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('121',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('123',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('124',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','100','101','107'])).

thf('126',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('128',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('129',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('132',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('134',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('135',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('136',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','100','101','107'])).

thf('138',plain,
    ( ( k2_funct_1 @ sk_B_1 )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95','100','101','107'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('140',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('141',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('143',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X33 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('146',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('147',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['141','147'])).

thf('149',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['114','117','118','124','125','126','132','133','136','137','138','148'])).

thf('150',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['33','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['98','99'])).

thf('152',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('154',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','154'])).

thf('156',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('157',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('160',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('161',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('162',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('163',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','164'])).

thf('166',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['159','165'])).

thf('167',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('168',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','168'])).

thf('170',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('171',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('178',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('179',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('180',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('182',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('183',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('184',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('185',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['184','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['183','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['182','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['181','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['98','99'])).

thf('197',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('199',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('200',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('201',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('202',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('204',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X33 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('205',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('207',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('208',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['202','208'])).

thf('210',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196','197','198','199','209'])).

thf('211',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['180','210'])).

thf('212',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('213',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('214',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['212','215'])).

thf('217',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('218',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('219',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('220',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['98','99'])).

thf('222',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['216','217','218','219','220','221'])).

thf('223',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('224',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('225',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('226',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['211','222','223','224','225'])).

thf('227',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['176','177','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','164'])).

thf('229',plain,(
    $false ),
    inference(demod,[status(thm)],['169','227','228'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZKdq08vJBd
% 0.12/0.37  % Computer   : n006.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 18:07:38 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 392 iterations in 0.249s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.49/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.49/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.49/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.49/0.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.49/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.72  thf(t88_funct_2, conjecture,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72       ( ( r2_relset_1 @
% 0.49/0.72           A @ A @ 
% 0.49/0.72           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.49/0.72           ( k6_partfun1 @ A ) ) & 
% 0.49/0.72         ( r2_relset_1 @
% 0.49/0.72           A @ A @ 
% 0.49/0.72           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.49/0.72           ( k6_partfun1 @ A ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i,B:$i]:
% 0.49/0.72        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72            ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72          ( ( r2_relset_1 @
% 0.49/0.72              A @ A @ 
% 0.49/0.72              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.49/0.72              ( k6_partfun1 @ A ) ) & 
% 0.49/0.72            ( r2_relset_1 @
% 0.49/0.72              A @ A @ 
% 0.49/0.72              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.49/0.72              ( k6_partfun1 @ A ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.49/0.72           (k6_partfun1 @ sk_A))
% 0.49/0.72        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.72              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.72             (k6_partfun1 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.72            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.49/0.72           (k6_partfun1 @ sk_A)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.72                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.49/0.72               (k6_partfun1 @ sk_A))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(redefinition_k2_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.72       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X30 : $i, X31 : $i]:
% 0.49/0.72         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.49/0.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.49/0.72          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.49/0.72          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.49/0.73          | ~ (v1_funct_1 @ X30))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.49/0.73  thf('4', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.73  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('6', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('7', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('9', plain,
% 0.49/0.73      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73            (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73           (k6_partfun1 @ sk_A)))
% 0.49/0.73         <= (~
% 0.49/0.73             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.49/0.73               (k6_partfun1 @ sk_A))))),
% 0.49/0.73      inference('demod', [status(thm)], ['1', '8'])).
% 0.49/0.73  thf('10', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('11', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(dt_k2_funct_2, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.73         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.73       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.49/0.73         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.49/0.73         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.49/0.73         ( m1_subset_1 @
% 0.49/0.73           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.49/0.73  thf('12', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((m1_subset_1 @ (k2_funct_2 @ X22 @ X23) @ 
% 0.49/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('13', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.49/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.73  thf('14', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('15', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('16', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('18', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf(redefinition_k1_partfun1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.73     ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.73         ( v1_funct_1 @ F ) & 
% 0.49/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.49/0.73       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.49/0.73  thf('19', plain,
% 0.49/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.49/0.73          | ~ (v1_funct_1 @ X24)
% 0.49/0.73          | ~ (v1_funct_1 @ X27)
% 0.49/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.49/0.73          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.49/0.73              = (k5_relat_1 @ X24 @ X27)))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.49/0.73  thf('20', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.49/0.73            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.73  thf('21', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('22', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((v1_funct_1 @ (k2_funct_2 @ X22 @ X23))
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('23', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.73  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('25', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('26', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('27', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.49/0.73  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('30', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.49/0.73            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.73          | ~ (v1_funct_1 @ X0))),
% 0.49/0.73      inference('demod', [status(thm)], ['20', '29'])).
% 0.49/0.73  thf('31', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['10', '30'])).
% 0.49/0.73  thf('32', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(t65_funct_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.73       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.49/0.73  thf('33', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X7)
% 0.49/0.73          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.49/0.73          | ~ (v1_funct_1 @ X7)
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.73  thf('34', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X7)
% 0.49/0.73          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.49/0.73          | ~ (v1_funct_1 @ X7)
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.73  thf('35', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('36', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((m1_subset_1 @ (k2_funct_2 @ X22 @ X23) @ 
% 0.49/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('37', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.73  thf('38', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('39', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('40', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((v1_funct_2 @ (k2_funct_2 @ X22 @ X23) @ X22 @ X22)
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('41', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.49/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.73  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('43', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('44', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('45', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('46', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.49/0.73  thf('47', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('48', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((v3_funct_2 @ (k2_funct_2 @ X22 @ X23) @ X22 @ X22)
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('49', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.49/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.73  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('51', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('52', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('53', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('54', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.49/0.73  thf('55', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['37', '38', '46', '54'])).
% 0.49/0.73  thf('56', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('57', plain,
% 0.49/0.73      (![X30 : $i, X31 : $i]:
% 0.49/0.73         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.49/0.73          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.49/0.73          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.49/0.73          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.49/0.73          | ~ (v1_funct_1 @ X30))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.49/0.73  thf('58', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73            = (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.49/0.73  thf('59', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('60', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.49/0.73  thf('61', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.49/0.73  thf('62', plain,
% 0.49/0.73      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.49/0.73  thf('63', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['55', '62'])).
% 0.49/0.73  thf('64', plain,
% 0.49/0.73      (![X30 : $i, X31 : $i]:
% 0.49/0.73         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.49/0.73          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.49/0.73          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.49/0.73          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.49/0.73          | ~ (v1_funct_1 @ X30))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.49/0.73  thf('65', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.49/0.73        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.49/0.73  thf('66', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('67', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((v1_funct_1 @ (k2_funct_2 @ X22 @ X23))
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('68', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.49/0.73  thf('69', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('70', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.49/0.73  thf('71', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.49/0.73  thf('72', plain,
% 0.49/0.73      ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.49/0.73  thf('73', plain,
% 0.49/0.73      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.49/0.73  thf('74', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.73  thf('75', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('76', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((v1_funct_2 @ (k2_funct_2 @ X22 @ X23) @ X22 @ X22)
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('77', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ 
% 0.49/0.73           sk_A))),
% 0.49/0.73      inference('sup-', [status(thm)], ['75', '76'])).
% 0.49/0.73  thf('78', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('79', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.49/0.73  thf('80', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.49/0.73  thf('81', plain,
% 0.49/0.73      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.49/0.73  thf('82', plain,
% 0.49/0.73      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.49/0.73  thf('83', plain,
% 0.49/0.73      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['81', '82'])).
% 0.49/0.73  thf('84', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('85', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i]:
% 0.49/0.73         ((v3_funct_2 @ (k2_funct_2 @ X22 @ X23) @ X22 @ X22)
% 0.49/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.49/0.73          | ~ (v3_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_2 @ X23 @ X22 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X23))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.73  thf('86', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ 
% 0.49/0.73           sk_A))),
% 0.49/0.73      inference('sup-', [status(thm)], ['84', '85'])).
% 0.49/0.73  thf('87', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('88', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.49/0.73  thf('89', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.49/0.73  thf('90', plain,
% 0.49/0.73      ((v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.49/0.73  thf('91', plain,
% 0.49/0.73      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.49/0.73  thf('92', plain,
% 0.49/0.73      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.73  thf('93', plain,
% 0.49/0.73      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)], ['65', '74', '83', '92'])).
% 0.49/0.73  thf('94', plain,
% 0.49/0.73      ((((k2_funct_2 @ sk_A @ sk_B_1)
% 0.49/0.73          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.49/0.73        | ~ (v1_relat_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup+', [status(thm)], ['34', '93'])).
% 0.49/0.73  thf('95', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('96', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(cc2_relat_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( v1_relat_1 @ A ) =>
% 0.49/0.73       ( ![B:$i]:
% 0.49/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.49/0.73  thf('97', plain,
% 0.49/0.73      (![X1 : $i, X2 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.49/0.73          | (v1_relat_1 @ X1)
% 0.49/0.73          | ~ (v1_relat_1 @ X2))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.73  thf('98', plain,
% 0.49/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['96', '97'])).
% 0.49/0.73  thf(fc6_relat_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.73  thf('99', plain,
% 0.49/0.73      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.49/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.73  thf('100', plain, ((v1_relat_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.73  thf('101', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('102', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(cc2_funct_2, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.73       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.73         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.49/0.73  thf('103', plain,
% 0.49/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.73         (~ (v1_funct_1 @ X19)
% 0.49/0.73          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 0.49/0.73          | (v2_funct_1 @ X19)
% 0.49/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.73  thf('104', plain,
% 0.49/0.73      (((v2_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['102', '103'])).
% 0.49/0.73  thf('105', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('106', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('107', plain, ((v2_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.49/0.73  thf('108', plain,
% 0.49/0.73      (((k2_funct_1 @ sk_B_1)
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)], ['94', '95', '100', '101', '107'])).
% 0.49/0.73  thf('109', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X7)
% 0.49/0.73          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.49/0.73          | ~ (v1_funct_1 @ X7)
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.73  thf(t61_funct_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.73       ( ( v2_funct_1 @ A ) =>
% 0.49/0.73         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.49/0.73             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.49/0.73           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.49/0.73             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.73  thf('110', plain,
% 0.49/0.73      (![X5 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X5)
% 0.49/0.73          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.49/0.73              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.49/0.73          | ~ (v1_funct_1 @ X5)
% 0.49/0.73          | ~ (v1_relat_1 @ X5))),
% 0.49/0.73      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.73  thf(redefinition_k6_partfun1, axiom,
% 0.49/0.73    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.49/0.73  thf('111', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.73  thf('112', plain,
% 0.49/0.73      (![X5 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X5)
% 0.49/0.73          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.49/0.73              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 0.49/0.73          | ~ (v1_funct_1 @ X5)
% 0.49/0.73          | ~ (v1_relat_1 @ X5))),
% 0.49/0.73      inference('demod', [status(thm)], ['110', '111'])).
% 0.49/0.73  thf('113', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.49/0.73            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['109', '112'])).
% 0.49/0.73  thf('114', plain,
% 0.49/0.73      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.49/0.73        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))
% 0.49/0.73        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))) @ 
% 0.49/0.73            (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73            = (k6_partfun1 @ 
% 0.49/0.73               (k1_relat_1 @ 
% 0.49/0.73                (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['108', '113'])).
% 0.49/0.73  thf('115', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf(cc1_relset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.73       ( v1_relat_1 @ C ) ))).
% 0.49/0.73  thf('116', plain,
% 0.49/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((v1_relat_1 @ X8)
% 0.49/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.73  thf('117', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.73  thf('118', plain,
% 0.49/0.73      (((k2_funct_1 @ sk_B_1)
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)], ['94', '95', '100', '101', '107'])).
% 0.49/0.73  thf('119', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('120', plain,
% 0.49/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.73         (~ (v1_funct_1 @ X19)
% 0.49/0.73          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 0.49/0.73          | (v2_funct_1 @ X19)
% 0.49/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.73  thf('121', plain,
% 0.49/0.73      (((v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['119', '120'])).
% 0.49/0.73  thf('122', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.49/0.73  thf('123', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('124', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.49/0.73  thf('125', plain,
% 0.49/0.73      (((k2_funct_1 @ sk_B_1)
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)], ['94', '95', '100', '101', '107'])).
% 0.49/0.73  thf('126', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('127', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['55', '62'])).
% 0.49/0.73  thf('128', plain,
% 0.49/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.73         (~ (v1_funct_1 @ X19)
% 0.49/0.73          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 0.49/0.73          | (v2_funct_1 @ X19)
% 0.49/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.73  thf('129', plain,
% 0.49/0.73      (((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.49/0.73        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['127', '128'])).
% 0.49/0.73  thf('130', plain,
% 0.49/0.73      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.73  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.73  thf('132', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.49/0.73  thf('133', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.73  thf('134', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['55', '62'])).
% 0.49/0.73  thf('135', plain,
% 0.49/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.73         ((v1_relat_1 @ X8)
% 0.49/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.73  thf('136', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['134', '135'])).
% 0.49/0.73  thf('137', plain,
% 0.49/0.73      (((k2_funct_1 @ sk_B_1)
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)], ['94', '95', '100', '101', '107'])).
% 0.49/0.73  thf('138', plain,
% 0.49/0.73      (((k2_funct_1 @ sk_B_1)
% 0.49/0.73         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)], ['94', '95', '100', '101', '107'])).
% 0.49/0.73  thf('139', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.73  thf('140', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.73         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.49/0.73          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.73  thf('141', plain,
% 0.49/0.73      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73         = (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['139', '140'])).
% 0.49/0.73  thf('142', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf(t67_funct_2, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.73       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.49/0.73  thf('143', plain,
% 0.49/0.73      (![X33 : $i, X34 : $i]:
% 0.49/0.73         (((k1_relset_1 @ X33 @ X33 @ X34) = (X33))
% 0.49/0.73          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.49/0.73          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.49/0.73          | ~ (v1_funct_1 @ X34))),
% 0.49/0.73      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.49/0.73  thf('144', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.49/0.73        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['142', '143'])).
% 0.49/0.73  thf('145', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('146', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.49/0.73  thf('147', plain,
% 0.49/0.73      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.49/0.73      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.49/0.73  thf('148', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.49/0.73      inference('sup+', [status(thm)], ['141', '147'])).
% 0.49/0.73  thf('149', plain,
% 0.49/0.73      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73         (k2_funct_1 @ (k2_funct_1 @ sk_B_1))) = (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('demod', [status(thm)],
% 0.49/0.73                ['114', '117', '118', '124', '125', '126', '132', '133', 
% 0.49/0.73                 '136', '137', '138', '148'])).
% 0.49/0.73  thf('150', plain,
% 0.49/0.73      ((((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_partfun1 @ sk_A))
% 0.49/0.73        | ~ (v1_relat_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup+', [status(thm)], ['33', '149'])).
% 0.49/0.73  thf('151', plain, ((v1_relat_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.73  thf('152', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('153', plain, ((v2_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.49/0.73  thf('154', plain,
% 0.49/0.73      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 0.49/0.73  thf('155', plain,
% 0.49/0.73      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73         sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('demod', [status(thm)], ['31', '32', '154'])).
% 0.49/0.73  thf('156', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.49/0.73  thf('157', plain,
% 0.49/0.73      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.73            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.73           (k6_partfun1 @ sk_A)))
% 0.49/0.73         <= (~
% 0.49/0.73             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.73                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.73               (k6_partfun1 @ sk_A))))),
% 0.49/0.73      inference('split', [status(esa)], ['0'])).
% 0.49/0.73  thf('158', plain,
% 0.49/0.73      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73            sk_B_1) @ 
% 0.49/0.73           (k6_partfun1 @ sk_A)))
% 0.49/0.73         <= (~
% 0.49/0.73             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.73                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.73               (k6_partfun1 @ sk_A))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['156', '157'])).
% 0.49/0.73  thf('159', plain,
% 0.49/0.73      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.49/0.73           (k6_partfun1 @ sk_A)))
% 0.49/0.73         <= (~
% 0.49/0.73             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.73                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.73               (k6_partfun1 @ sk_A))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['155', '158'])).
% 0.49/0.73  thf(t29_relset_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( m1_subset_1 @
% 0.49/0.73       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.49/0.73  thf('160', plain,
% 0.49/0.73      (![X18 : $i]:
% 0.49/0.73         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 0.49/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.49/0.73  thf('161', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.73  thf('162', plain,
% 0.49/0.73      (![X18 : $i]:
% 0.49/0.73         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 0.49/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.49/0.73      inference('demod', [status(thm)], ['160', '161'])).
% 0.49/0.73  thf(reflexivity_r2_relset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.73     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.73       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.49/0.73  thf('163', plain,
% 0.49/0.73      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.49/0.73         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.49/0.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.49/0.73          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.49/0.73      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.49/0.73  thf('164', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.49/0.73      inference('condensation', [status(thm)], ['163'])).
% 0.49/0.73  thf('165', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['162', '164'])).
% 0.49/0.73  thf('166', plain,
% 0.49/0.73      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.73          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.73         (k6_partfun1 @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['159', '165'])).
% 0.49/0.73  thf('167', plain,
% 0.49/0.73      (~
% 0.49/0.73       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.49/0.73         (k6_partfun1 @ sk_A))) | 
% 0.49/0.73       ~
% 0.49/0.73       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.49/0.73          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.49/0.73         (k6_partfun1 @ sk_A)))),
% 0.49/0.73      inference('split', [status(esa)], ['0'])).
% 0.49/0.73  thf('168', plain,
% 0.49/0.73      (~
% 0.49/0.73       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.49/0.73         (k6_partfun1 @ sk_A)))),
% 0.49/0.73      inference('sat_resolution*', [status(thm)], ['166', '167'])).
% 0.49/0.73  thf('169', plain,
% 0.49/0.73      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.49/0.73          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73           (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73          (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('simpl_trail', [status(thm)], ['9', '168'])).
% 0.49/0.73  thf('170', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.49/0.73  thf('171', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('172', plain,
% 0.49/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.49/0.73          | ~ (v1_funct_1 @ X24)
% 0.49/0.73          | ~ (v1_funct_1 @ X27)
% 0.49/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.49/0.73          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.49/0.73              = (k5_relat_1 @ X24 @ X27)))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.49/0.73  thf('173', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.49/0.73            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['171', '172'])).
% 0.49/0.73  thf('174', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('175', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.49/0.73            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.49/0.73          | ~ (v1_funct_1 @ X0))),
% 0.49/0.73      inference('demod', [status(thm)], ['173', '174'])).
% 0.49/0.73  thf('176', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73            (k2_funct_1 @ sk_B_1))
% 0.49/0.73            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['170', '175'])).
% 0.49/0.73  thf('177', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('178', plain,
% 0.49/0.73      (![X5 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X5)
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.49/0.73              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.49/0.73          | ~ (v1_funct_1 @ X5)
% 0.49/0.73          | ~ (v1_relat_1 @ X5))),
% 0.49/0.73      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.73  thf('179', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.49/0.73  thf('180', plain,
% 0.49/0.73      (![X5 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X5)
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.49/0.73              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 0.49/0.73          | ~ (v1_funct_1 @ X5)
% 0.49/0.73          | ~ (v1_relat_1 @ X5))),
% 0.49/0.73      inference('demod', [status(thm)], ['178', '179'])).
% 0.49/0.73  thf('181', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf(t62_funct_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.73       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.49/0.73  thf('182', plain,
% 0.49/0.73      (![X6 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X6)
% 0.49/0.73          | (v2_funct_1 @ (k2_funct_1 @ X6))
% 0.49/0.73          | ~ (v1_funct_1 @ X6)
% 0.49/0.73          | ~ (v1_relat_1 @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.49/0.73  thf('183', plain,
% 0.49/0.73      (![X6 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X6)
% 0.49/0.73          | (v2_funct_1 @ (k2_funct_1 @ X6))
% 0.49/0.73          | ~ (v1_funct_1 @ X6)
% 0.49/0.73          | ~ (v1_relat_1 @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.49/0.73  thf('184', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X7)
% 0.49/0.73          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.49/0.73          | ~ (v1_funct_1 @ X7)
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.73  thf('185', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X7)
% 0.49/0.73          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.49/0.73          | ~ (v1_funct_1 @ X7)
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.73  thf('186', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.49/0.73            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['109', '112'])).
% 0.49/0.73  thf('187', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['185', '186'])).
% 0.49/0.73  thf('188', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['187'])).
% 0.49/0.73  thf('189', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['184', '188'])).
% 0.49/0.73  thf('190', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['189'])).
% 0.49/0.73  thf('191', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['183', '190'])).
% 0.49/0.73  thf('192', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.73      inference('simplify', [status(thm)], ['191'])).
% 0.49/0.73  thf('193', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['182', '192'])).
% 0.49/0.73  thf('194', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.49/0.73            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ X0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['193'])).
% 0.49/0.73  thf('195', plain,
% 0.49/0.73      ((~ (v1_relat_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v2_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73            (k2_funct_1 @ sk_B_1))
% 0.49/0.73            = (k6_partfun1 @ 
% 0.49/0.73               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['181', '194'])).
% 0.49/0.73  thf('196', plain, ((v1_relat_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.73  thf('197', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('198', plain, ((v2_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.49/0.73  thf('199', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.73  thf('200', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['55', '62'])).
% 0.49/0.73  thf('201', plain,
% 0.49/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.73         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.49/0.73          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.73  thf('202', plain,
% 0.49/0.73      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['200', '201'])).
% 0.49/0.73  thf('203', plain,
% 0.49/0.73      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['55', '62'])).
% 0.49/0.73  thf('204', plain,
% 0.49/0.73      (![X33 : $i, X34 : $i]:
% 0.49/0.73         (((k1_relset_1 @ X33 @ X33 @ X34) = (X33))
% 0.49/0.73          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.49/0.73          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.49/0.73          | ~ (v1_funct_1 @ X34))),
% 0.49/0.73      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.49/0.73  thf('205', plain,
% 0.49/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)
% 0.49/0.73        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73            = (sk_A)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['203', '204'])).
% 0.49/0.73  thf('206', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.73  thf('207', plain,
% 0.49/0.73      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ sk_A @ sk_A)),
% 0.49/0.73      inference('demod', [status(thm)], ['81', '82'])).
% 0.49/0.73  thf('208', plain,
% 0.49/0.73      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73         = (sk_A))),
% 0.49/0.73      inference('demod', [status(thm)], ['205', '206', '207'])).
% 0.49/0.73  thf('209', plain,
% 0.49/0.73      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1))) = (sk_A))),
% 0.49/0.73      inference('sup+', [status(thm)], ['202', '208'])).
% 0.49/0.73  thf('210', plain,
% 0.49/0.73      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B_1)) @ 
% 0.49/0.73         (k2_funct_1 @ sk_B_1)) = (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('demod', [status(thm)],
% 0.49/0.73                ['195', '196', '197', '198', '199', '209'])).
% 0.49/0.73  thf('211', plain,
% 0.49/0.73      ((((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))
% 0.49/0.73          = (k6_partfun1 @ sk_A))
% 0.49/0.73        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['180', '210'])).
% 0.49/0.73  thf('212', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.73  thf('213', plain,
% 0.49/0.73      (![X7 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X7)
% 0.49/0.73          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.49/0.73          | ~ (v1_funct_1 @ X7)
% 0.49/0.73          | ~ (v1_relat_1 @ X7))),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.73  thf('214', plain,
% 0.49/0.73      (![X5 : $i]:
% 0.49/0.73         (~ (v2_funct_1 @ X5)
% 0.49/0.73          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.49/0.73              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 0.49/0.73          | ~ (v1_funct_1 @ X5)
% 0.49/0.73          | ~ (v1_relat_1 @ X5))),
% 0.49/0.73      inference('demod', [status(thm)], ['178', '179'])).
% 0.49/0.73  thf('215', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.49/0.73            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.49/0.73          | ~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | ~ (v2_funct_1 @ X0)
% 0.49/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.73          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['213', '214'])).
% 0.49/0.73  thf('216', plain,
% 0.49/0.73      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73        | ~ (v2_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_B_1)
% 0.49/0.73        | ~ (v1_relat_1 @ sk_B_1)
% 0.49/0.73        | ((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['212', '215'])).
% 0.49/0.73  thf('217', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.49/0.73  thf('218', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('219', plain, ((v2_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.49/0.73  thf('220', plain, ((v1_funct_1 @ sk_B_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('221', plain, ((v1_relat_1 @ sk_B_1)),
% 0.49/0.73      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.73  thf('222', plain,
% 0.49/0.73      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.49/0.73         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.49/0.73      inference('demod', [status(thm)],
% 0.49/0.73                ['216', '217', '218', '219', '220', '221'])).
% 0.49/0.73  thf('223', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.73  thf('224', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.73  thf('225', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.49/0.73  thf('226', plain,
% 0.49/0.73      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) = (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('demod', [status(thm)], ['211', '222', '223', '224', '225'])).
% 0.49/0.73  thf('227', plain,
% 0.49/0.73      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.49/0.73         (k2_funct_1 @ sk_B_1)) = (k6_partfun1 @ sk_A))),
% 0.49/0.73      inference('demod', [status(thm)], ['176', '177', '226'])).
% 0.49/0.73  thf('228', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['162', '164'])).
% 0.49/0.73  thf('229', plain, ($false),
% 0.49/0.73      inference('demod', [status(thm)], ['169', '227', '228'])).
% 0.49/0.73  
% 0.49/0.73  % SZS output end Refutation
% 0.49/0.73  
% 0.49/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
