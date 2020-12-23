%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xrpw8MUtux

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:23 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 557 expanded)
%              Number of leaves         :   37 ( 186 expanded)
%              Depth                    :   16
%              Number of atoms          : 1522 (12891 expanded)
%              Number of equality atoms :   41 (  95 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

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
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('32',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('33',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('50',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_2 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('56',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_2 @ X17 @ X16 )
      | ( ( k2_relat_1 @ X17 )
        = X16 )
      | ~ ( v5_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['61','66','69'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('71',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('72',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('74',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( r2_relset_1 @ X10 @ X11 @ X9 @ X12 )
      | ( X9 != X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('75',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('81',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','70','76','77','78','84'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('87',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['38','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','88'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_2 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('93',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('101',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('103',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['93','101','102'])).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_2 @ X17 @ X16 )
      | ( ( k2_relat_1 @ X17 )
        = X16 )
      | ~ ( v5_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('110',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('112',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['105','110','113'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('117',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('121',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('122',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['89','119','120','121','122','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xrpw8MUtux
% 0.15/0.37  % Computer   : n016.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:08:34 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.77/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/1.01  % Solved by: fo/fo7.sh
% 0.77/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.01  % done 174 iterations in 0.522s
% 0.77/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/1.01  % SZS output start Refutation
% 0.77/1.01  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.77/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.77/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/1.01  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.77/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/1.01  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.77/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/1.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.77/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/1.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.77/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.77/1.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.77/1.01  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.77/1.01  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.77/1.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.77/1.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.77/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.77/1.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.77/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.01  thf(t61_funct_1, axiom,
% 0.77/1.01    (![A:$i]:
% 0.77/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/1.01       ( ( v2_funct_1 @ A ) =>
% 0.77/1.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.77/1.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.77/1.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.77/1.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.77/1.01  thf('0', plain,
% 0.77/1.01      (![X5 : $i]:
% 0.77/1.01         (~ (v2_funct_1 @ X5)
% 0.77/1.01          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.77/1.01              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.77/1.01          | ~ (v1_funct_1 @ X5)
% 0.77/1.01          | ~ (v1_relat_1 @ X5))),
% 0.77/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.77/1.01  thf(t88_funct_2, conjecture,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.77/1.01         ( v3_funct_2 @ B @ A @ A ) & 
% 0.77/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.77/1.01       ( ( r2_relset_1 @
% 0.77/1.01           A @ A @ 
% 0.77/1.01           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.77/1.01           ( k6_partfun1 @ A ) ) & 
% 0.77/1.01         ( r2_relset_1 @
% 0.77/1.01           A @ A @ 
% 0.77/1.01           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.77/1.01           ( k6_partfun1 @ A ) ) ) ))).
% 0.77/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.01    (~( ![A:$i,B:$i]:
% 0.77/1.01        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.77/1.01            ( v3_funct_2 @ B @ A @ A ) & 
% 0.77/1.01            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.77/1.01          ( ( r2_relset_1 @
% 0.77/1.01              A @ A @ 
% 0.77/1.01              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.77/1.01              ( k6_partfun1 @ A ) ) & 
% 0.77/1.01            ( r2_relset_1 @
% 0.77/1.01              A @ A @ 
% 0.77/1.01              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.77/1.01              ( k6_partfun1 @ A ) ) ) ) )),
% 0.77/1.01    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.77/1.01  thf('1', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(dt_k2_funct_2, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.77/1.01         ( v3_funct_2 @ B @ A @ A ) & 
% 0.77/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.77/1.01       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.77/1.01         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.77/1.01         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.77/1.01         ( m1_subset_1 @
% 0.77/1.01           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.77/1.01  thf('2', plain,
% 0.77/1.01      (![X18 : $i, X19 : $i]:
% 0.77/1.01         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.77/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.77/1.01          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.77/1.01          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.77/1.01          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.77/1.01          | ~ (v1_funct_1 @ X19))),
% 0.77/1.01      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.77/1.01  thf('3', plain,
% 0.77/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.77/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/1.01  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('7', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(redefinition_k2_funct_2, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.77/1.01         ( v3_funct_2 @ B @ A @ A ) & 
% 0.77/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.77/1.01       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.77/1.01  thf('8', plain,
% 0.77/1.01      (![X28 : $i, X29 : $i]:
% 0.77/1.01         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.77/1.01          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.77/1.01          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.77/1.01          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.77/1.01          | ~ (v1_funct_1 @ X28))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.77/1.01  thf('9', plain,
% 0.77/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/1.01  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('11', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('12', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('13', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.77/1.01  thf('14', plain,
% 0.77/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.77/1.01  thf('15', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(redefinition_k1_partfun1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.77/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.77/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/1.01         ( v1_funct_1 @ F ) & 
% 0.77/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.77/1.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.77/1.01  thf('16', plain,
% 0.77/1.01      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.77/1.01         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.77/1.01          | ~ (v1_funct_1 @ X22)
% 0.77/1.01          | ~ (v1_funct_1 @ X25)
% 0.77/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.77/1.01          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.77/1.01              = (k5_relat_1 @ X22 @ X25)))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.77/1.01  thf('17', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.77/1.01            = (k5_relat_1 @ sk_B @ X0))
% 0.77/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/1.01          | ~ (v1_funct_1 @ X0)
% 0.77/1.01          | ~ (v1_funct_1 @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['15', '16'])).
% 0.77/1.01  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('19', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.77/1.01            = (k5_relat_1 @ sk_B @ X0))
% 0.77/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/1.01          | ~ (v1_funct_1 @ X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.77/1.01  thf('20', plain,
% 0.77/1.01      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.77/1.01        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['14', '19'])).
% 0.77/1.01  thf('21', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('22', plain,
% 0.77/1.01      (![X18 : $i, X19 : $i]:
% 0.77/1.01         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.77/1.01          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.77/1.01          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.77/1.01          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.77/1.01          | ~ (v1_funct_1 @ X19))),
% 0.77/1.01      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.77/1.01  thf('23', plain,
% 0.77/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/1.01  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('25', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('26', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('27', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.77/1.01  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.77/1.01  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/1.01  thf('30', plain,
% 0.77/1.01      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.77/1.01         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['20', '29'])).
% 0.77/1.01  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.77/1.01  thf('32', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01           (k6_partfun1 @ sk_A))
% 0.77/1.01        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01             (k6_partfun1 @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(redefinition_k6_partfun1, axiom,
% 0.77/1.01    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.77/1.01  thf('33', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/1.01  thf('34', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/1.01  thf('35', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01           (k6_relat_1 @ sk_A))
% 0.77/1.01        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01             (k6_relat_1 @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.77/1.01  thf('36', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01           (k6_relat_1 @ sk_A)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('split', [status(esa)], ['35'])).
% 0.77/1.01  thf('37', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01            (k2_funct_1 @ sk_B)) @ 
% 0.77/1.01           (k6_relat_1 @ sk_A)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['31', '36'])).
% 0.77/1.01  thf('38', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['30', '37'])).
% 0.77/1.01  thf('39', plain,
% 0.77/1.01      (![X5 : $i]:
% 0.77/1.01         (~ (v2_funct_1 @ X5)
% 0.77/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.77/1.01              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.77/1.01          | ~ (v1_funct_1 @ X5)
% 0.77/1.01          | ~ (v1_relat_1 @ X5))),
% 0.77/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.77/1.01  thf('40', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('41', plain,
% 0.77/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.77/1.01  thf('42', plain,
% 0.77/1.01      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.77/1.01         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.77/1.01          | ~ (v1_funct_1 @ X22)
% 0.77/1.01          | ~ (v1_funct_1 @ X25)
% 0.77/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.77/1.01          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.77/1.01              = (k5_relat_1 @ X22 @ X25)))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.77/1.01  thf('43', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.77/1.01            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.77/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/1.01          | ~ (v1_funct_1 @ X0)
% 0.77/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['41', '42'])).
% 0.77/1.01  thf('44', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/1.01  thf('45', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.77/1.01            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.77/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.77/1.01          | ~ (v1_funct_1 @ X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['43', '44'])).
% 0.77/1.01  thf('46', plain,
% 0.77/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['40', '45'])).
% 0.77/1.01  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('48', plain,
% 0.77/1.01      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.77/1.01         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['46', '47'])).
% 0.77/1.01  thf('49', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.77/1.01  thf('50', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01           (k6_relat_1 @ sk_A)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('split', [status(esa)], ['35'])).
% 0.77/1.01  thf('51', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01            sk_B) @ 
% 0.77/1.01           (k6_relat_1 @ sk_A)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['49', '50'])).
% 0.77/1.01  thf('52', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['48', '51'])).
% 0.77/1.01  thf('53', plain,
% 0.77/1.01      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.77/1.01            (k6_relat_1 @ sk_A))
% 0.77/1.01         | ~ (v1_relat_1 @ sk_B)
% 0.77/1.01         | ~ (v1_funct_1 @ sk_B)
% 0.77/1.01         | ~ (v2_funct_1 @ sk_B)))
% 0.77/1.01         <= (~
% 0.77/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01               (k6_relat_1 @ sk_A))))),
% 0.77/1.01      inference('sup-', [status(thm)], ['39', '52'])).
% 0.77/1.01  thf('54', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(cc2_funct_2, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/1.01       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.77/1.01         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.77/1.01  thf('55', plain,
% 0.77/1.01      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/1.01         (~ (v1_funct_1 @ X13)
% 0.77/1.01          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 0.77/1.01          | (v2_funct_2 @ X13 @ X15)
% 0.77/1.01          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.77/1.01  thf('56', plain,
% 0.77/1.01      (((v2_funct_2 @ sk_B @ sk_A)
% 0.77/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v1_funct_1 @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['54', '55'])).
% 0.77/1.01  thf('57', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('59', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.77/1.01      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.77/1.01  thf(d3_funct_2, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.77/1.01       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.77/1.01  thf('60', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         (~ (v2_funct_2 @ X17 @ X16)
% 0.77/1.01          | ((k2_relat_1 @ X17) = (X16))
% 0.77/1.01          | ~ (v5_relat_1 @ X17 @ X16)
% 0.77/1.01          | ~ (v1_relat_1 @ X17))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.77/1.01  thf('61', plain,
% 0.77/1.01      ((~ (v1_relat_1 @ sk_B)
% 0.77/1.01        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.77/1.01        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['59', '60'])).
% 0.77/1.01  thf('62', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(cc2_relat_1, axiom,
% 0.77/1.01    (![A:$i]:
% 0.77/1.01     ( ( v1_relat_1 @ A ) =>
% 0.77/1.01       ( ![B:$i]:
% 0.77/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.77/1.01  thf('63', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.77/1.01          | (v1_relat_1 @ X0)
% 0.77/1.01          | ~ (v1_relat_1 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.77/1.01  thf('64', plain,
% 0.77/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/1.01  thf(fc6_relat_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.77/1.01  thf('65', plain,
% 0.77/1.01      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.77/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/1.01  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['64', '65'])).
% 0.77/1.01  thf('67', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(cc2_relset_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/1.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.77/1.01  thf('68', plain,
% 0.77/1.01      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/1.01         ((v5_relat_1 @ X6 @ X8)
% 0.77/1.01          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/1.01  thf('69', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.77/1.01      inference('sup-', [status(thm)], ['67', '68'])).
% 0.77/1.01  thf('70', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['61', '66', '69'])).
% 0.77/1.01  thf(dt_k6_partfun1, axiom,
% 0.77/1.01    (![A:$i]:
% 0.77/1.01     ( ( m1_subset_1 @
% 0.77/1.01         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.77/1.01       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.77/1.01  thf('71', plain,
% 0.77/1.01      (![X21 : $i]:
% 0.77/1.01         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 0.77/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.77/1.01      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.77/1.01  thf('72', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/1.01  thf('73', plain,
% 0.77/1.01      (![X21 : $i]:
% 0.77/1.01         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 0.77/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.77/1.01      inference('demod', [status(thm)], ['71', '72'])).
% 0.77/1.01  thf(redefinition_r2_relset_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/1.01       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.77/1.01  thf('74', plain,
% 0.77/1.01      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.77/1.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.77/1.01          | (r2_relset_1 @ X10 @ X11 @ X9 @ X12)
% 0.77/1.01          | ((X9) != (X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.77/1.01  thf('75', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.77/1.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.77/1.01      inference('simplify', [status(thm)], ['74'])).
% 0.77/1.01  thf('76', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['73', '75'])).
% 0.77/1.01  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['64', '65'])).
% 0.77/1.01  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('79', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('80', plain,
% 0.77/1.01      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/1.01         (~ (v1_funct_1 @ X13)
% 0.77/1.01          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 0.77/1.01          | (v2_funct_1 @ X13)
% 0.77/1.01          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.77/1.01  thf('81', plain,
% 0.77/1.01      (((v2_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v1_funct_1 @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['79', '80'])).
% 0.77/1.01  thf('82', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.77/1.01  thf('85', plain,
% 0.77/1.01      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01         (k6_relat_1 @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['53', '70', '76', '77', '78', '84'])).
% 0.77/1.01  thf('86', plain,
% 0.77/1.01      (~
% 0.77/1.01       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01         (k6_relat_1 @ sk_A))) | 
% 0.77/1.01       ~
% 0.77/1.01       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.77/1.01          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.77/1.01         (k6_relat_1 @ sk_A)))),
% 0.77/1.01      inference('split', [status(esa)], ['35'])).
% 0.77/1.01  thf('87', plain,
% 0.77/1.01      (~
% 0.77/1.01       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.77/1.01          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.77/1.01         (k6_relat_1 @ sk_A)))),
% 0.77/1.01      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 0.77/1.01  thf('88', plain,
% 0.77/1.01      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.77/1.01          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['38', '87'])).
% 0.77/1.01  thf('89', plain,
% 0.77/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.77/1.01           (k6_relat_1 @ sk_A))
% 0.77/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.77/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v2_funct_1 @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['0', '88'])).
% 0.77/1.01  thf(t55_funct_1, axiom,
% 0.77/1.01    (![A:$i]:
% 0.77/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/1.01       ( ( v2_funct_1 @ A ) =>
% 0.77/1.01         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.77/1.01           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/1.01  thf('90', plain,
% 0.77/1.01      (![X4 : $i]:
% 0.77/1.01         (~ (v2_funct_1 @ X4)
% 0.77/1.01          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.77/1.01          | ~ (v1_funct_1 @ X4)
% 0.77/1.01          | ~ (v1_relat_1 @ X4))),
% 0.77/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/1.01  thf('91', plain,
% 0.77/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.77/1.01  thf('92', plain,
% 0.77/1.01      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/1.01         (~ (v1_funct_1 @ X13)
% 0.77/1.01          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 0.77/1.01          | (v2_funct_2 @ X13 @ X15)
% 0.77/1.01          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.77/1.01  thf('93', plain,
% 0.77/1.01      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.77/1.01        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['91', '92'])).
% 0.77/1.01  thf('94', plain,
% 0.77/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('95', plain,
% 0.77/1.01      (![X18 : $i, X19 : $i]:
% 0.77/1.01         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.77/1.01          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.77/1.01          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.77/1.01          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.77/1.01          | ~ (v1_funct_1 @ X19))),
% 0.77/1.01      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.77/1.01  thf('96', plain,
% 0.77/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.77/1.01        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.77/1.01      inference('sup-', [status(thm)], ['94', '95'])).
% 0.77/1.01  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('98', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('99', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('100', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.77/1.01  thf('101', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.77/1.01      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.77/1.01  thf('102', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/1.01  thf('103', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.77/1.01      inference('demod', [status(thm)], ['93', '101', '102'])).
% 0.77/1.01  thf('104', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         (~ (v2_funct_2 @ X17 @ X16)
% 0.77/1.01          | ((k2_relat_1 @ X17) = (X16))
% 0.77/1.01          | ~ (v5_relat_1 @ X17 @ X16)
% 0.77/1.01          | ~ (v1_relat_1 @ X17))),
% 0.77/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.77/1.01  thf('105', plain,
% 0.77/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.77/1.01        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.77/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['103', '104'])).
% 0.77/1.01  thf('106', plain,
% 0.77/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.77/1.01  thf('107', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.77/1.01          | (v1_relat_1 @ X0)
% 0.77/1.01          | ~ (v1_relat_1 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.77/1.01  thf('108', plain,
% 0.77/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.77/1.01        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['106', '107'])).
% 0.77/1.01  thf('109', plain,
% 0.77/1.01      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.77/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/1.01  thf('110', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['108', '109'])).
% 0.77/1.01  thf('111', plain,
% 0.77/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.77/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.77/1.01  thf('112', plain,
% 0.77/1.01      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/1.01         ((v5_relat_1 @ X6 @ X8)
% 0.77/1.01          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.77/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/1.01  thf('113', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.77/1.01      inference('sup-', [status(thm)], ['111', '112'])).
% 0.77/1.01  thf('114', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['105', '110', '113'])).
% 0.77/1.01  thf('115', plain,
% 0.77/1.01      ((((k1_relat_1 @ sk_B) = (sk_A))
% 0.77/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.77/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.77/1.01        | ~ (v2_funct_1 @ sk_B))),
% 0.77/1.01      inference('sup+', [status(thm)], ['90', '114'])).
% 0.77/1.01  thf('116', plain, ((v1_relat_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['64', '65'])).
% 0.77/1.01  thf('117', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('118', plain, ((v2_funct_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.77/1.01  thf('119', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.77/1.01  thf('120', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['73', '75'])).
% 0.77/1.01  thf('121', plain, ((v1_relat_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['64', '65'])).
% 0.77/1.01  thf('122', plain, ((v1_funct_1 @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('123', plain, ((v2_funct_1 @ sk_B)),
% 0.77/1.01      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.77/1.01  thf('124', plain, ($false),
% 0.77/1.01      inference('demod', [status(thm)],
% 0.77/1.01                ['89', '119', '120', '121', '122', '123'])).
% 0.77/1.01  
% 0.77/1.01  % SZS output end Refutation
% 0.77/1.01  
% 0.77/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
