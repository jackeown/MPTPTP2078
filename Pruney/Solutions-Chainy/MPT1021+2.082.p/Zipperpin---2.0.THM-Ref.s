%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A42MoQSoWa

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:24 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  181 (1049 expanded)
%              Number of leaves         :   36 ( 335 expanded)
%              Depth                    :   15
%              Number of atoms          : 1727 (26012 expanded)
%              Number of equality atoms :   55 ( 165 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf('41',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

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
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('54',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('56',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','54','55'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('74',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('84',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['72','85'])).

thf('87',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','56','57','63','64','69','86'])).

thf('88',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','87'])).

thf('89',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('95',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('96',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','100'])).

thf('102',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('113',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('114',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('115',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','54','55'])).

thf('119',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('120',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('123',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122'])).

thf('124',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('125',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122'])).

thf('126',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('134',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['129','130','131','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('137',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('139',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','135','136','137','138'])).

thf('140',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['123','139'])).

thf('141',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['104','141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A42MoQSoWa
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.79  % Solved by: fo/fo7.sh
% 0.55/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.79  % done 380 iterations in 0.312s
% 0.55/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.79  % SZS output start Refutation
% 0.55/0.79  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.79  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.55/0.79  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.55/0.79  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.55/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.55/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.79  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.55/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.79  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.55/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.79  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.79  thf(t88_funct_2, conjecture,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.79       ( ( r2_relset_1 @
% 0.55/0.79           A @ A @ 
% 0.55/0.79           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.55/0.79           ( k6_partfun1 @ A ) ) & 
% 0.55/0.79         ( r2_relset_1 @
% 0.55/0.79           A @ A @ 
% 0.55/0.79           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.55/0.79           ( k6_partfun1 @ A ) ) ) ))).
% 0.55/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.79    (~( ![A:$i,B:$i]:
% 0.55/0.79        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.79            ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.79            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.79          ( ( r2_relset_1 @
% 0.55/0.79              A @ A @ 
% 0.55/0.79              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.55/0.79              ( k6_partfun1 @ A ) ) & 
% 0.55/0.79            ( r2_relset_1 @
% 0.55/0.79              A @ A @ 
% 0.55/0.79              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.55/0.79              ( k6_partfun1 @ A ) ) ) ) )),
% 0.55/0.79    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.55/0.79  thf('0', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79           (k6_partfun1 @ sk_A))
% 0.55/0.79        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79             (k6_partfun1 @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('1', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79           (k6_partfun1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('split', [status(esa)], ['0'])).
% 0.55/0.79  thf(redefinition_k6_partfun1, axiom,
% 0.55/0.79    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.55/0.79  thf('2', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.79  thf('3', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79           (k6_relat_1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.79  thf('4', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(redefinition_k2_funct_2, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.79       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.55/0.79  thf('5', plain,
% 0.55/0.79      (![X29 : $i, X30 : $i]:
% 0.55/0.79         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.55/0.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.55/0.79          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.55/0.79          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.55/0.79          | ~ (v1_funct_1 @ X29))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.55/0.79  thf('6', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.79  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.79  thf('11', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79            (k2_funct_1 @ sk_B)) @ 
% 0.55/0.79           (k6_relat_1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('demod', [status(thm)], ['3', '10'])).
% 0.55/0.79  thf('12', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('13', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(dt_k2_funct_2, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( v3_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.79       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.55/0.79         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.55/0.79         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.55/0.79         ( m1_subset_1 @
% 0.55/0.79           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.55/0.79  thf('14', plain,
% 0.55/0.79      (![X17 : $i, X18 : $i]:
% 0.55/0.79         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 0.55/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.55/0.79          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_1 @ X18))),
% 0.55/0.79      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.55/0.79  thf('15', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.55/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.79  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.79  thf('20', plain,
% 0.55/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.55/0.79  thf(redefinition_k1_partfun1, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.79     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.79         ( v1_funct_1 @ F ) & 
% 0.55/0.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.55/0.79       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.55/0.79  thf('21', plain,
% 0.55/0.79      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.55/0.79          | ~ (v1_funct_1 @ X23)
% 0.55/0.79          | ~ (v1_funct_1 @ X26)
% 0.55/0.79          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.55/0.79          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.55/0.79              = (k5_relat_1 @ X23 @ X26)))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.55/0.79  thf('22', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.55/0.79            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.55/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.79          | ~ (v1_funct_1 @ X0)
% 0.55/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.79  thf('23', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('24', plain,
% 0.55/0.79      (![X17 : $i, X18 : $i]:
% 0.55/0.79         ((v1_funct_1 @ (k2_funct_2 @ X17 @ X18))
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.55/0.79          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_1 @ X18))),
% 0.55/0.79      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.55/0.79  thf('25', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.79  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.55/0.79  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.79  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.79  thf('32', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.55/0.79            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.55/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.79          | ~ (v1_funct_1 @ X0))),
% 0.55/0.79      inference('demod', [status(thm)], ['22', '31'])).
% 0.55/0.79  thf('33', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['12', '32'])).
% 0.55/0.79  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('35', plain,
% 0.55/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.55/0.79  thf(cc2_relat_1, axiom,
% 0.55/0.79    (![A:$i]:
% 0.55/0.79     ( ( v1_relat_1 @ A ) =>
% 0.55/0.79       ( ![B:$i]:
% 0.55/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.79  thf('36', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.79          | (v1_relat_1 @ X0)
% 0.55/0.79          | ~ (v1_relat_1 @ X1))),
% 0.55/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.79  thf('37', plain,
% 0.55/0.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.55/0.79        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.79  thf(fc6_relat_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.79  thf('38', plain,
% 0.55/0.79      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.79  thf('39', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.79  thf(t65_funct_1, axiom,
% 0.55/0.79    (![A:$i]:
% 0.55/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.79       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.55/0.79  thf('40', plain,
% 0.55/0.79      (![X6 : $i]:
% 0.55/0.79         (~ (v2_funct_1 @ X6)
% 0.55/0.79          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.55/0.79          | ~ (v1_funct_1 @ X6)
% 0.55/0.79          | ~ (v1_relat_1 @ X6))),
% 0.55/0.79      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.79  thf(t61_funct_1, axiom,
% 0.55/0.79    (![A:$i]:
% 0.55/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.79       ( ( v2_funct_1 @ A ) =>
% 0.55/0.79         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.55/0.79             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.55/0.79           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.55/0.79             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.79  thf('41', plain,
% 0.55/0.79      (![X4 : $i]:
% 0.55/0.79         (~ (v2_funct_1 @ X4)
% 0.55/0.79          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.55/0.79              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.55/0.79          | ~ (v1_funct_1 @ X4)
% 0.55/0.79          | ~ (v1_relat_1 @ X4))),
% 0.55/0.79      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.79  thf('42', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.55/0.79            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.55/0.79          | ~ (v1_relat_1 @ X0)
% 0.55/0.79          | ~ (v1_funct_1 @ X0)
% 0.55/0.79          | ~ (v2_funct_1 @ X0)
% 0.55/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.79          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['40', '41'])).
% 0.55/0.79  thf('43', plain,
% 0.55/0.79      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ~ (v2_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.79        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.55/0.79            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['39', '42'])).
% 0.55/0.79  thf('44', plain,
% 0.55/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.55/0.79  thf(cc2_funct_2, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i]:
% 0.55/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.79       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.55/0.79         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.55/0.79  thf('45', plain,
% 0.55/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.79         (~ (v1_funct_1 @ X14)
% 0.55/0.79          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.55/0.79          | (v2_funct_1 @ X14)
% 0.55/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.55/0.79      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.55/0.79  thf('46', plain,
% 0.55/0.79      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['44', '45'])).
% 0.55/0.79  thf('47', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('48', plain,
% 0.55/0.79      (![X17 : $i, X18 : $i]:
% 0.55/0.79         ((v3_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.55/0.79          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_1 @ X18))),
% 0.55/0.79      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.55/0.79  thf('49', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.55/0.79      inference('sup-', [status(thm)], ['47', '48'])).
% 0.55/0.79  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('51', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('52', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('53', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.79  thf('54', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.55/0.79      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.55/0.79  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.79  thf('56', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['46', '54', '55'])).
% 0.55/0.79  thf('57', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.79  thf('58', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('59', plain,
% 0.55/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.79         (~ (v1_funct_1 @ X14)
% 0.55/0.79          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.55/0.79          | (v2_funct_1 @ X14)
% 0.55/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.55/0.79      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.55/0.79  thf('60', plain,
% 0.55/0.79      (((v2_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v1_funct_1 @ sk_B))),
% 0.55/0.79      inference('sup-', [status(thm)], ['58', '59'])).
% 0.55/0.79  thf('61', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.79      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.55/0.79  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('65', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('66', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.79          | (v1_relat_1 @ X0)
% 0.55/0.79          | ~ (v1_relat_1 @ X1))),
% 0.55/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.79  thf('67', plain,
% 0.55/0.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.55/0.79      inference('sup-', [status(thm)], ['65', '66'])).
% 0.55/0.79  thf('68', plain,
% 0.55/0.79      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.79  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.79      inference('demod', [status(thm)], ['67', '68'])).
% 0.55/0.79  thf('70', plain,
% 0.55/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.55/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i]:
% 0.55/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.79  thf('71', plain,
% 0.55/0.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.55/0.79         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.55/0.79          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.79  thf('72', plain,
% 0.55/0.79      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.55/0.79         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.79  thf('73', plain,
% 0.55/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.55/0.79  thf(t67_funct_2, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.55/0.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.55/0.79       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.55/0.79  thf('74', plain,
% 0.55/0.79      (![X32 : $i, X33 : $i]:
% 0.55/0.79         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.55/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.55/0.79          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.55/0.79          | ~ (v1_funct_1 @ X33))),
% 0.55/0.79      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.55/0.79  thf('75', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.55/0.79        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['73', '74'])).
% 0.55/0.79  thf('76', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.79  thf('77', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('78', plain,
% 0.55/0.79      (![X17 : $i, X18 : $i]:
% 0.55/0.79         ((v1_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 0.55/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.55/0.79          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.55/0.79          | ~ (v1_funct_1 @ X18))),
% 0.55/0.79      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.55/0.79  thf('79', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.55/0.79      inference('sup-', [status(thm)], ['77', '78'])).
% 0.55/0.79  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('81', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('82', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.79  thf('84', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.55/0.79      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.55/0.79  thf('85', plain,
% 0.55/0.79      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.79      inference('demod', [status(thm)], ['75', '76', '84'])).
% 0.55/0.79  thf('86', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.55/0.79      inference('sup+', [status(thm)], ['72', '85'])).
% 0.55/0.79  thf('87', plain,
% 0.55/0.79      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.55/0.79      inference('demod', [status(thm)],
% 0.55/0.79                ['43', '56', '57', '63', '64', '69', '86'])).
% 0.55/0.79  thf('88', plain,
% 0.55/0.79      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.55/0.79         = (k6_relat_1 @ sk_A))),
% 0.55/0.79      inference('demod', [status(thm)], ['33', '34', '87'])).
% 0.55/0.79  thf('89', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.55/0.79  thf('90', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79           (k6_partfun1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('split', [status(esa)], ['0'])).
% 0.55/0.79  thf('91', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.79  thf('92', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79           (k6_relat_1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('demod', [status(thm)], ['90', '91'])).
% 0.55/0.79  thf('93', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79            sk_B) @ 
% 0.55/0.79           (k6_relat_1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['89', '92'])).
% 0.55/0.79  thf('94', plain,
% 0.55/0.79      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.55/0.79           (k6_relat_1 @ sk_A)))
% 0.55/0.79         <= (~
% 0.55/0.79             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79               (k6_partfun1 @ sk_A))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['88', '93'])).
% 0.55/0.79  thf(dt_k6_partfun1, axiom,
% 0.55/0.79    (![A:$i]:
% 0.55/0.79     ( ( m1_subset_1 @
% 0.55/0.79         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.55/0.79       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.55/0.79  thf('95', plain,
% 0.55/0.79      (![X20 : $i]:
% 0.55/0.79         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 0.55/0.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.55/0.79      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.55/0.79  thf('96', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.79  thf('97', plain,
% 0.55/0.79      (![X20 : $i]:
% 0.55/0.79         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 0.55/0.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.55/0.79      inference('demod', [status(thm)], ['95', '96'])).
% 0.55/0.79  thf(reflexivity_r2_relset_1, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.79     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.79       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.55/0.79  thf('98', plain,
% 0.55/0.79      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.79         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.55/0.79          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.55/0.79          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.55/0.79      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.55/0.79  thf('99', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.55/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.55/0.79      inference('condensation', [status(thm)], ['98'])).
% 0.55/0.79  thf('100', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.55/0.79      inference('sup-', [status(thm)], ['97', '99'])).
% 0.55/0.79  thf('101', plain,
% 0.55/0.79      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79         (k6_partfun1 @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['94', '100'])).
% 0.55/0.79  thf('102', plain,
% 0.55/0.79      (~
% 0.55/0.79       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79         (k6_partfun1 @ sk_A))) | 
% 0.55/0.79       ~
% 0.55/0.79       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.55/0.79          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.55/0.79         (k6_partfun1 @ sk_A)))),
% 0.55/0.79      inference('split', [status(esa)], ['0'])).
% 0.55/0.79  thf('103', plain,
% 0.55/0.79      (~
% 0.55/0.79       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.55/0.79         (k6_partfun1 @ sk_A)))),
% 0.55/0.79      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 0.55/0.79  thf('104', plain,
% 0.55/0.79      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.79          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.55/0.79          (k6_relat_1 @ sk_A))),
% 0.55/0.79      inference('simpl_trail', [status(thm)], ['11', '103'])).
% 0.55/0.79  thf('105', plain,
% 0.55/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.55/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.55/0.79  thf('106', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('107', plain,
% 0.55/0.79      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.79         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.55/0.79          | ~ (v1_funct_1 @ X23)
% 0.55/0.79          | ~ (v1_funct_1 @ X26)
% 0.55/0.79          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.55/0.79          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.55/0.79              = (k5_relat_1 @ X23 @ X26)))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.55/0.79  thf('108', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.55/0.79            = (k5_relat_1 @ sk_B @ X0))
% 0.55/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.79          | ~ (v1_funct_1 @ X0)
% 0.55/0.79          | ~ (v1_funct_1 @ sk_B))),
% 0.55/0.79      inference('sup-', [status(thm)], ['106', '107'])).
% 0.55/0.79  thf('109', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('110', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.55/0.79            = (k5_relat_1 @ sk_B @ X0))
% 0.55/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.79          | ~ (v1_funct_1 @ X0))),
% 0.55/0.79      inference('demod', [status(thm)], ['108', '109'])).
% 0.55/0.79  thf('111', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.55/0.79            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['105', '110'])).
% 0.55/0.79  thf('112', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.79  thf('113', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.79  thf('114', plain,
% 0.55/0.79      (![X6 : $i]:
% 0.55/0.79         (~ (v2_funct_1 @ X6)
% 0.55/0.79          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.55/0.79          | ~ (v1_funct_1 @ X6)
% 0.55/0.79          | ~ (v1_relat_1 @ X6))),
% 0.55/0.79      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.79  thf('115', plain,
% 0.55/0.79      (![X4 : $i]:
% 0.55/0.79         (~ (v2_funct_1 @ X4)
% 0.55/0.79          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.55/0.79              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.55/0.79          | ~ (v1_funct_1 @ X4)
% 0.55/0.79          | ~ (v1_relat_1 @ X4))),
% 0.55/0.79      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.79  thf('116', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.55/0.79            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.55/0.79          | ~ (v1_relat_1 @ X0)
% 0.55/0.79          | ~ (v1_funct_1 @ X0)
% 0.55/0.79          | ~ (v2_funct_1 @ X0)
% 0.55/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.79          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['114', '115'])).
% 0.55/0.79  thf('117', plain,
% 0.55/0.79      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.55/0.79        | ~ (v2_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.79        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.55/0.79            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.55/0.79      inference('sup-', [status(thm)], ['113', '116'])).
% 0.55/0.79  thf('118', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['46', '54', '55'])).
% 0.55/0.79  thf('119', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.79  thf('120', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.79      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.55/0.79  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.79      inference('demod', [status(thm)], ['67', '68'])).
% 0.55/0.79  thf('123', plain,
% 0.55/0.79      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.55/0.79         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.55/0.79      inference('demod', [status(thm)],
% 0.55/0.79                ['117', '118', '119', '120', '121', '122'])).
% 0.55/0.79  thf('124', plain,
% 0.55/0.79      (![X4 : $i]:
% 0.55/0.79         (~ (v2_funct_1 @ X4)
% 0.55/0.79          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.55/0.79              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.55/0.79          | ~ (v1_funct_1 @ X4)
% 0.55/0.79          | ~ (v1_relat_1 @ X4))),
% 0.55/0.79      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.79  thf('125', plain,
% 0.55/0.79      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.55/0.79         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.55/0.79      inference('demod', [status(thm)],
% 0.55/0.79                ['117', '118', '119', '120', '121', '122'])).
% 0.55/0.79  thf('126', plain,
% 0.55/0.79      ((((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.55/0.79          = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 0.55/0.79        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v2_funct_1 @ sk_B))),
% 0.55/0.79      inference('sup+', [status(thm)], ['124', '125'])).
% 0.55/0.79  thf('127', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('128', plain,
% 0.55/0.79      (![X32 : $i, X33 : $i]:
% 0.55/0.79         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.55/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.55/0.79          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.55/0.79          | ~ (v1_funct_1 @ X33))),
% 0.55/0.79      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.55/0.79  thf('129', plain,
% 0.55/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.55/0.79        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.55/0.79        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.55/0.79      inference('sup-', [status(thm)], ['127', '128'])).
% 0.55/0.79  thf('130', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('131', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('132', plain,
% 0.55/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('133', plain,
% 0.55/0.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.55/0.79         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.55/0.79          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.55/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.79  thf('134', plain,
% 0.55/0.79      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.55/0.79      inference('sup-', [status(thm)], ['132', '133'])).
% 0.55/0.79  thf('135', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.55/0.79      inference('demod', [status(thm)], ['129', '130', '131', '134'])).
% 0.55/0.79  thf('136', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.79      inference('demod', [status(thm)], ['67', '68'])).
% 0.55/0.79  thf('137', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf('138', plain, ((v2_funct_1 @ sk_B)),
% 0.55/0.79      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.55/0.79  thf('139', plain,
% 0.55/0.79      (((k6_relat_1 @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.55/0.79      inference('demod', [status(thm)], ['126', '135', '136', '137', '138'])).
% 0.55/0.79  thf('140', plain,
% 0.55/0.79      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.55/0.79      inference('demod', [status(thm)], ['123', '139'])).
% 0.55/0.79  thf('141', plain,
% 0.55/0.79      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.55/0.79         = (k6_relat_1 @ sk_A))),
% 0.55/0.79      inference('demod', [status(thm)], ['111', '112', '140'])).
% 0.55/0.79  thf('142', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.55/0.79      inference('sup-', [status(thm)], ['97', '99'])).
% 0.55/0.79  thf('143', plain, ($false),
% 0.55/0.79      inference('demod', [status(thm)], ['104', '141', '142'])).
% 0.55/0.79  
% 0.55/0.79  % SZS output end Refutation
% 0.55/0.79  
% 0.63/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
