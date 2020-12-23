%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f6wve8tdKY

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:19 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  218 (2057 expanded)
%              Number of leaves         :   36 ( 642 expanded)
%              Depth                    :   19
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

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
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
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('44',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

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
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','44','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('58',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('59',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('60',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','60'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','60'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('65',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('71',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('72',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('73',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('75',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('80',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('81',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('82',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('84',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['66','75','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['63','85'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('87',plain,(
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

thf('88',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('90',plain,(
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

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('93',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('94',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('95',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
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
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('108',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('109',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('111',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('115',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('116',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('119',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('123',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('130',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','119','120','126','127','130'])).

thf('132',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('134',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('135',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['106','131','132','133','134'])).

thf('136',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','32','135'])).

thf('137',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('138',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('139',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('141',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('142',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('143',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('144',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('147',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['140','146'])).

thf('148',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('149',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('153',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('161',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('163',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('164',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('165',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['128','129'])).

thf('167',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('168',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('169',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('171',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('172',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('174',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('175',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['169','175'])).

thf('177',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166','176'])).

thf('178',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['150','178','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f6wve8tdKY
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.85  % Solved by: fo/fo7.sh
% 0.60/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.85  % done 590 iterations in 0.397s
% 0.60/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.85  % SZS output start Refutation
% 0.60/0.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.60/0.85  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.60/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.85  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.60/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.85  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.60/0.85  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.85  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.60/0.85  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.60/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.60/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.60/0.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.60/0.85  thf(t88_funct_2, conjecture,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( v3_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.60/0.85       ( ( r2_relset_1 @
% 0.60/0.85           A @ A @ 
% 0.60/0.85           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.60/0.85           ( k6_partfun1 @ A ) ) & 
% 0.60/0.85         ( r2_relset_1 @
% 0.60/0.85           A @ A @ 
% 0.60/0.85           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.60/0.85           ( k6_partfun1 @ A ) ) ) ))).
% 0.60/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.85    (~( ![A:$i,B:$i]:
% 0.60/0.85        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.60/0.85            ( v3_funct_2 @ B @ A @ A ) & 
% 0.60/0.85            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.60/0.85          ( ( r2_relset_1 @
% 0.60/0.85              A @ A @ 
% 0.60/0.85              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.60/0.85              ( k6_partfun1 @ A ) ) & 
% 0.60/0.85            ( r2_relset_1 @
% 0.60/0.85              A @ A @ 
% 0.60/0.85              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.60/0.85              ( k6_partfun1 @ A ) ) ) ) )),
% 0.60/0.85    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.60/0.85  thf('0', plain,
% 0.60/0.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.85            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.85           (k6_partfun1 @ sk_A))
% 0.60/0.85        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.85             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.60/0.85              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.60/0.85             (k6_partfun1 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('1', plain,
% 0.60/0.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.60/0.85            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.60/0.85           (k6_partfun1 @ sk_A)))
% 0.60/0.85         <= (~
% 0.60/0.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.60/0.85                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.60/0.85               (k6_partfun1 @ sk_A))))),
% 0.60/0.85      inference('split', [status(esa)], ['0'])).
% 0.60/0.85  thf('2', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(redefinition_k2_funct_2, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( v3_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.60/0.85       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.60/0.85  thf('3', plain,
% 0.60/0.85      (![X28 : $i, X29 : $i]:
% 0.60/0.85         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.60/0.85          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.60/0.85          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.60/0.85          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.60/0.85          | ~ (v1_funct_1 @ X28))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.60/0.85  thf('4', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ sk_B)
% 0.60/0.85        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.85  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.85  thf('9', plain,
% 0.60/0.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.85           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.85            sk_B) @ 
% 0.60/0.85           (k6_partfun1 @ sk_A)))
% 0.60/0.85         <= (~
% 0.60/0.85             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.85               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.60/0.85                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.60/0.85               (k6_partfun1 @ sk_A))))),
% 0.60/0.85      inference('demod', [status(thm)], ['1', '8'])).
% 0.60/0.85  thf('10', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(dt_k2_funct_2, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( v3_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.60/0.85       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.60/0.85         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.60/0.85         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.60/0.85         ( m1_subset_1 @
% 0.60/0.85           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.60/0.85  thf('11', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('12', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ sk_B)
% 0.60/0.85        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.85  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('14', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('15', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('16', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.85  thf('17', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.85  thf('18', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(redefinition_k1_partfun1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.85     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.85         ( v1_funct_1 @ F ) & 
% 0.60/0.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.60/0.85       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.60/0.85  thf('19', plain,
% 0.60/0.85      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.60/0.85          | ~ (v1_funct_1 @ X22)
% 0.60/0.85          | ~ (v1_funct_1 @ X25)
% 0.60/0.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.60/0.85          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.60/0.85              = (k5_relat_1 @ X22 @ X25)))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.60/0.85  thf('20', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.60/0.85            = (k5_relat_1 @ sk_B @ X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.60/0.85          | ~ (v1_funct_1 @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.85  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('22', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.60/0.85            = (k5_relat_1 @ sk_B @ X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.60/0.85          | ~ (v1_funct_1 @ X0))),
% 0.60/0.85      inference('demod', [status(thm)], ['20', '21'])).
% 0.60/0.85  thf('23', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.85        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.85            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['17', '22'])).
% 0.60/0.85  thf('24', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('25', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('26', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ sk_B)
% 0.60/0.85        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.85  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.60/0.85  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.85  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.85  thf('33', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.85  thf('34', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('35', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.85        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.85  thf('36', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.85  thf('37', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('38', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('39', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ sk_B)
% 0.60/0.85        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.85  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('41', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('42', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('43', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.85  thf('44', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('46', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ sk_B)
% 0.60/0.85        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.85        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.85  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('50', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.85  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.60/0.85  thf('53', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['35', '36', '44', '52'])).
% 0.60/0.85  thf('54', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.85  thf('55', plain,
% 0.60/0.85      (![X28 : $i, X29 : $i]:
% 0.60/0.85         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.60/0.85          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.60/0.85          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.60/0.85          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.60/0.85          | ~ (v1_funct_1 @ X28))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.85        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.60/0.85            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['54', '55'])).
% 0.60/0.85  thf('57', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.85  thf('58', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.60/0.85  thf('59', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.60/0.85  thf('60', plain,
% 0.60/0.85      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.60/0.85         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.60/0.85  thf('61', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['53', '60'])).
% 0.60/0.85  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.85         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.60/0.85          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.85  thf('63', plain,
% 0.60/0.85      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.60/0.85         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['61', '62'])).
% 0.60/0.85  thf('64', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['53', '60'])).
% 0.60/0.85  thf(t67_funct_2, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.60/0.85       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.60/0.85  thf('65', plain,
% 0.60/0.85      (![X31 : $i, X32 : $i]:
% 0.60/0.85         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.60/0.85          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.60/0.85          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.60/0.85          | ~ (v1_funct_1 @ X32))),
% 0.60/0.85      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.60/0.85  thf('66', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.60/0.85        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.60/0.85        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.60/0.85            = (sk_A)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['64', '65'])).
% 0.60/0.85  thf('67', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.85  thf('68', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('69', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.85        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.85  thf('70', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.85  thf('71', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.60/0.85  thf('72', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.60/0.85  thf('73', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.60/0.85  thf('74', plain,
% 0.60/0.85      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.60/0.85         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.60/0.85  thf('75', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['73', '74'])).
% 0.60/0.85  thf('76', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.85  thf('77', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.60/0.85          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X19))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.60/0.85  thf('78', plain,
% 0.60/0.85      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.85        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.85        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['76', '77'])).
% 0.60/0.85  thf('79', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.85  thf('80', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.60/0.85  thf('81', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.60/0.85  thf('82', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.60/0.85  thf('83', plain,
% 0.60/0.85      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.60/0.85         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.60/0.85  thf('84', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['82', '83'])).
% 0.60/0.85  thf('85', plain,
% 0.60/0.85      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.60/0.85         = (sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['66', '75', '84'])).
% 0.60/0.85  thf('86', plain,
% 0.60/0.85      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) = (sk_A))),
% 0.60/0.85      inference('sup+', [status(thm)], ['63', '85'])).
% 0.60/0.85  thf(t61_funct_1, axiom,
% 0.60/0.86    (![A:$i]:
% 0.60/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.86       ( ( v2_funct_1 @ A ) =>
% 0.60/0.86         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.60/0.86             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.60/0.86           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.60/0.86             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.60/0.86  thf('87', plain,
% 0.60/0.86      (![X1 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X1)
% 0.60/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.60/0.86              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X1)
% 0.60/0.86          | ~ (v1_relat_1 @ X1))),
% 0.60/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.60/0.86  thf(redefinition_k6_partfun1, axiom,
% 0.60/0.86    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.60/0.86  thf('88', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.60/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.86  thf('89', plain,
% 0.60/0.86      (![X1 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X1)
% 0.60/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.60/0.86              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X1)
% 0.60/0.86          | ~ (v1_relat_1 @ X1))),
% 0.60/0.86      inference('demod', [status(thm)], ['87', '88'])).
% 0.60/0.86  thf(t62_funct_1, axiom,
% 0.60/0.86    (![A:$i]:
% 0.60/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.86       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.60/0.86  thf('90', plain,
% 0.60/0.86      (![X2 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X2)
% 0.60/0.86          | (v2_funct_1 @ (k2_funct_1 @ X2))
% 0.60/0.86          | ~ (v1_funct_1 @ X2)
% 0.60/0.86          | ~ (v1_relat_1 @ X2))),
% 0.60/0.86      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.60/0.86  thf(dt_k2_funct_1, axiom,
% 0.60/0.86    (![A:$i]:
% 0.60/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.86       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.60/0.86         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.60/0.86  thf('91', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0))),
% 0.60/0.86      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.60/0.86  thf('92', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0))),
% 0.60/0.86      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.60/0.86  thf(t65_funct_1, axiom,
% 0.60/0.86    (![A:$i]:
% 0.60/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.86       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.60/0.86  thf('93', plain,
% 0.60/0.86      (![X3 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X3)
% 0.60/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.60/0.86          | ~ (v1_funct_1 @ X3)
% 0.60/0.86          | ~ (v1_relat_1 @ X3))),
% 0.60/0.86      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.60/0.86  thf('94', plain,
% 0.60/0.86      (![X1 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X1)
% 0.60/0.86          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.60/0.86              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X1)
% 0.60/0.86          | ~ (v1_relat_1 @ X1))),
% 0.60/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.60/0.86  thf('95', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.60/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.86  thf('96', plain,
% 0.60/0.86      (![X1 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X1)
% 0.60/0.86          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.60/0.86              = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X1)
% 0.60/0.86          | ~ (v1_relat_1 @ X1))),
% 0.60/0.86      inference('demod', [status(thm)], ['94', '95'])).
% 0.60/0.86  thf('97', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['93', '96'])).
% 0.60/0.86  thf('98', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['92', '97'])).
% 0.60/0.86  thf('99', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0))),
% 0.60/0.86      inference('simplify', [status(thm)], ['98'])).
% 0.60/0.86  thf('100', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['91', '99'])).
% 0.60/0.86  thf('101', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0))),
% 0.60/0.86      inference('simplify', [status(thm)], ['100'])).
% 0.60/0.86  thf('102', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['90', '101'])).
% 0.60/0.86  thf('103', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0))),
% 0.60/0.86      inference('simplify', [status(thm)], ['102'])).
% 0.60/0.86  thf('104', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0))),
% 0.60/0.86      inference('sup+', [status(thm)], ['89', '103'])).
% 0.60/0.86  thf('105', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ((k6_partfun1 @ (k2_relat_1 @ X0))
% 0.60/0.86              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.60/0.86      inference('simplify', [status(thm)], ['104'])).
% 0.60/0.86  thf('106', plain,
% 0.60/0.86      ((((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.60/0.86          = (k6_partfun1 @ sk_A))
% 0.60/0.86        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['86', '105'])).
% 0.60/0.86  thf('107', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.86  thf(cc1_relset_1, axiom,
% 0.60/0.86    (![A:$i,B:$i,C:$i]:
% 0.60/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.86       ( v1_relat_1 @ C ) ))).
% 0.60/0.86  thf('108', plain,
% 0.60/0.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.86         ((v1_relat_1 @ X4)
% 0.60/0.86          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.60/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.86  thf('109', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['107', '108'])).
% 0.60/0.86  thf('110', plain,
% 0.60/0.86      (![X3 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X3)
% 0.60/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.60/0.86          | ~ (v1_funct_1 @ X3)
% 0.60/0.86          | ~ (v1_relat_1 @ X3))),
% 0.60/0.86      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.60/0.86  thf('111', plain,
% 0.60/0.86      (![X1 : $i]:
% 0.60/0.86         (~ (v2_funct_1 @ X1)
% 0.60/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.60/0.86              = (k6_partfun1 @ (k2_relat_1 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X1)
% 0.60/0.86          | ~ (v1_relat_1 @ X1))),
% 0.60/0.86      inference('demod', [status(thm)], ['87', '88'])).
% 0.60/0.86  thf('112', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.60/0.86            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['110', '111'])).
% 0.60/0.86  thf('113', plain,
% 0.60/0.86      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v2_funct_1 @ sk_B)
% 0.60/0.86        | ~ (v1_funct_1 @ sk_B)
% 0.60/0.86        | ~ (v1_relat_1 @ sk_B)
% 0.60/0.86        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.60/0.86            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['109', '112'])).
% 0.60/0.86  thf('114', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.86  thf(cc2_funct_2, axiom,
% 0.60/0.86    (![A:$i,B:$i,C:$i]:
% 0.60/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.86       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.60/0.86         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.60/0.86  thf('115', plain,
% 0.60/0.86      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.86         (~ (v1_funct_1 @ X15)
% 0.60/0.86          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.60/0.86          | (v2_funct_1 @ X15)
% 0.60/0.86          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.60/0.86      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.60/0.86  thf('116', plain,
% 0.60/0.86      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['114', '115'])).
% 0.60/0.86  thf('117', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.86      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.60/0.86  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.86  thf('119', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.60/0.86  thf('120', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.86  thf('121', plain,
% 0.60/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('122', plain,
% 0.60/0.86      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.86         (~ (v1_funct_1 @ X15)
% 0.60/0.86          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.60/0.86          | (v2_funct_1 @ X15)
% 0.60/0.86          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.60/0.86      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.60/0.86  thf('123', plain,
% 0.60/0.86      (((v2_funct_1 @ sk_B)
% 0.60/0.86        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.60/0.86        | ~ (v1_funct_1 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['121', '122'])).
% 0.60/0.86  thf('124', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('126', plain, ((v2_funct_1 @ sk_B)),
% 0.60/0.86      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.60/0.86  thf('127', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('128', plain,
% 0.60/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('129', plain,
% 0.60/0.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.86         ((v1_relat_1 @ X4)
% 0.60/0.86          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.60/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.86  thf('130', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.86      inference('sup-', [status(thm)], ['128', '129'])).
% 0.60/0.86  thf('131', plain,
% 0.60/0.86      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.60/0.86         = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.60/0.86      inference('demod', [status(thm)],
% 0.60/0.86                ['113', '119', '120', '126', '127', '130'])).
% 0.60/0.86  thf('132', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['107', '108'])).
% 0.60/0.86  thf('133', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.86  thf('134', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.60/0.86  thf('135', plain,
% 0.60/0.86      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_partfun1 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['106', '131', '132', '133', '134'])).
% 0.60/0.86  thf('136', plain,
% 0.60/0.86      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.60/0.86         = (k6_partfun1 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['23', '32', '135'])).
% 0.60/0.86  thf('137', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.86  thf('138', plain,
% 0.60/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.86           (k6_partfun1 @ sk_A)))
% 0.60/0.86         <= (~
% 0.60/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.86               (k6_partfun1 @ sk_A))))),
% 0.60/0.86      inference('split', [status(esa)], ['0'])).
% 0.60/0.86  thf('139', plain,
% 0.60/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86            (k2_funct_1 @ sk_B)) @ 
% 0.60/0.86           (k6_partfun1 @ sk_A)))
% 0.60/0.86         <= (~
% 0.60/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.86               (k6_partfun1 @ sk_A))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['137', '138'])).
% 0.60/0.86  thf('140', plain,
% 0.60/0.86      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.60/0.86           (k6_partfun1 @ sk_A)))
% 0.60/0.86         <= (~
% 0.60/0.86             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.86               (k6_partfun1 @ sk_A))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['136', '139'])).
% 0.60/0.86  thf(t29_relset_1, axiom,
% 0.60/0.86    (![A:$i]:
% 0.60/0.86     ( m1_subset_1 @
% 0.60/0.86       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.60/0.86  thf('141', plain,
% 0.60/0.86      (![X14 : $i]:
% 0.60/0.86         (m1_subset_1 @ (k6_relat_1 @ X14) @ 
% 0.60/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.60/0.86      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.60/0.86  thf('142', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.60/0.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.86  thf('143', plain,
% 0.60/0.86      (![X14 : $i]:
% 0.60/0.86         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 0.60/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.60/0.86      inference('demod', [status(thm)], ['141', '142'])).
% 0.60/0.86  thf(reflexivity_r2_relset_1, axiom,
% 0.60/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.86     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.86       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.60/0.86  thf('144', plain,
% 0.60/0.86      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.86         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.60/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.60/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.60/0.86      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.60/0.86  thf('145', plain,
% 0.60/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.86         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.60/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.60/0.86      inference('condensation', [status(thm)], ['144'])).
% 0.60/0.86  thf('146', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.60/0.86      inference('sup-', [status(thm)], ['143', '145'])).
% 0.60/0.86  thf('147', plain,
% 0.60/0.86      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.86         (k6_partfun1 @ sk_A)))),
% 0.60/0.86      inference('demod', [status(thm)], ['140', '146'])).
% 0.60/0.86  thf('148', plain,
% 0.60/0.86      (~
% 0.60/0.86       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.60/0.86          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.60/0.86         (k6_partfun1 @ sk_A))) | 
% 0.60/0.86       ~
% 0.60/0.86       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.60/0.86          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.60/0.86         (k6_partfun1 @ sk_A)))),
% 0.60/0.86      inference('split', [status(esa)], ['0'])).
% 0.60/0.86  thf('149', plain,
% 0.60/0.86      (~
% 0.60/0.86       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.60/0.86          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.60/0.86         (k6_partfun1 @ sk_A)))),
% 0.60/0.86      inference('sat_resolution*', [status(thm)], ['147', '148'])).
% 0.60/0.86  thf('150', plain,
% 0.60/0.86      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.86          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.60/0.86          (k6_partfun1 @ sk_A))),
% 0.60/0.86      inference('simpl_trail', [status(thm)], ['9', '149'])).
% 0.60/0.86  thf('151', plain,
% 0.60/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('152', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.86  thf('153', plain,
% 0.60/0.86      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.60/0.86          | ~ (v1_funct_1 @ X22)
% 0.60/0.86          | ~ (v1_funct_1 @ X25)
% 0.60/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.60/0.86          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.60/0.86              = (k5_relat_1 @ X22 @ X25)))),
% 0.60/0.86      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.60/0.86  thf('154', plain,
% 0.60/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.86         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.60/0.86            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.60/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['152', '153'])).
% 0.60/0.86  thf('155', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.86  thf('156', plain,
% 0.60/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.86         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.60/0.86            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.60/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.60/0.86          | ~ (v1_funct_1 @ X0))),
% 0.60/0.86      inference('demod', [status(thm)], ['154', '155'])).
% 0.60/0.86  thf('157', plain,
% 0.60/0.86      ((~ (v1_funct_1 @ sk_B)
% 0.60/0.86        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.86            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['151', '156'])).
% 0.60/0.86  thf('158', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('159', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['107', '108'])).
% 0.60/0.86  thf('160', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.60/0.86          | ~ (v1_relat_1 @ X0)
% 0.60/0.86          | ~ (v1_funct_1 @ X0)
% 0.60/0.86          | ~ (v2_funct_1 @ X0)
% 0.60/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.60/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['93', '96'])).
% 0.60/0.86  thf('161', plain,
% 0.60/0.86      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v2_funct_1 @ sk_B)
% 0.60/0.86        | ~ (v1_funct_1 @ sk_B)
% 0.60/0.86        | ~ (v1_relat_1 @ sk_B)
% 0.60/0.86        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.60/0.86            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['159', '160'])).
% 0.60/0.86  thf('162', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.60/0.86  thf('163', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.86  thf('164', plain, ((v2_funct_1 @ sk_B)),
% 0.60/0.86      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.60/0.86  thf('165', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('166', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.86      inference('sup-', [status(thm)], ['128', '129'])).
% 0.60/0.86  thf('167', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.86  thf('168', plain,
% 0.60/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.86         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.60/0.86          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.60/0.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.86  thf('169', plain,
% 0.60/0.86      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.60/0.86         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['167', '168'])).
% 0.60/0.86  thf('170', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.60/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.86      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.60/0.86  thf('171', plain,
% 0.60/0.86      (![X31 : $i, X32 : $i]:
% 0.60/0.86         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.60/0.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.60/0.86          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.60/0.86          | ~ (v1_funct_1 @ X32))),
% 0.60/0.86      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.60/0.86  thf('172', plain,
% 0.60/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.60/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.60/0.86        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['170', '171'])).
% 0.60/0.86  thf('173', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.86  thf('174', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.60/0.86      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.60/0.86  thf('175', plain,
% 0.60/0.86      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.60/0.86  thf('176', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.60/0.86      inference('sup+', [status(thm)], ['169', '175'])).
% 0.60/0.86  thf('177', plain,
% 0.60/0.86      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_partfun1 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)],
% 0.60/0.86                ['161', '162', '163', '164', '165', '166', '176'])).
% 0.60/0.86  thf('178', plain,
% 0.60/0.86      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.60/0.86         = (k6_partfun1 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['157', '158', '177'])).
% 0.60/0.86  thf('179', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.60/0.86      inference('sup-', [status(thm)], ['143', '145'])).
% 0.60/0.86  thf('180', plain, ($false),
% 0.60/0.86      inference('demod', [status(thm)], ['150', '178', '179'])).
% 0.60/0.86  
% 0.60/0.86  % SZS output end Refutation
% 0.60/0.86  
% 0.70/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
