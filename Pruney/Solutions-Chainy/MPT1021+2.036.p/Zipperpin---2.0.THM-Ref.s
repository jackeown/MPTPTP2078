%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iO01irOCnj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:16 EST 2020

% Result     : Theorem 0.93s
% Output     : Refutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 542 expanded)
%              Number of leaves         :   36 ( 181 expanded)
%              Depth                    :   16
%              Number of atoms          : 1497 (12820 expanded)
%              Number of equality atoms :   41 (  95 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
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
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_2 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_2 @ X16 @ X15 )
      | ( ( k2_relat_1 @ X16 )
        = X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['61','64','67'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('69',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('70',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('71',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 )
      | ( X8 != X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('79',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','68','74','75','76','82'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('85',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['38','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','86'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('90',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_2 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('91',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('99',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('101',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['91','99','100'])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_2 @ X16 @ X15 )
      | ( ( k2_relat_1 @ X16 )
        = X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('105',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('106',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('108',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('109',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['103','106','109'])).

thf('111',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['88','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('117',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['87','115','116','117','118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iO01irOCnj
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.93/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.93/1.13  % Solved by: fo/fo7.sh
% 0.93/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.93/1.13  % done 174 iterations in 0.670s
% 0.93/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.93/1.13  % SZS output start Refutation
% 0.93/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.93/1.13  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.93/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.93/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.93/1.13  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.93/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.93/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.93/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.93/1.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.93/1.13  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.93/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.93/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.93/1.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.93/1.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.93/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.93/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.93/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.93/1.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.93/1.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.93/1.13  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.93/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.93/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.93/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.93/1.13  thf(t61_funct_1, axiom,
% 0.93/1.13    (![A:$i]:
% 0.93/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.93/1.13       ( ( v2_funct_1 @ A ) =>
% 0.93/1.13         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.93/1.13             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.93/1.13           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.93/1.13             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.93/1.13  thf('0', plain,
% 0.93/1.13      (![X1 : $i]:
% 0.93/1.13         (~ (v2_funct_1 @ X1)
% 0.93/1.13          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.93/1.13              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.93/1.13          | ~ (v1_funct_1 @ X1)
% 0.93/1.13          | ~ (v1_relat_1 @ X1))),
% 0.93/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.93/1.13  thf(t88_funct_2, conjecture,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.93/1.13         ( v3_funct_2 @ B @ A @ A ) & 
% 0.93/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.93/1.13       ( ( r2_relset_1 @
% 0.93/1.13           A @ A @ 
% 0.93/1.13           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.93/1.13           ( k6_partfun1 @ A ) ) & 
% 0.93/1.13         ( r2_relset_1 @
% 0.93/1.13           A @ A @ 
% 0.93/1.13           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.93/1.13           ( k6_partfun1 @ A ) ) ) ))).
% 0.93/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.93/1.13    (~( ![A:$i,B:$i]:
% 0.93/1.13        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.93/1.13            ( v3_funct_2 @ B @ A @ A ) & 
% 0.93/1.13            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.93/1.13          ( ( r2_relset_1 @
% 0.93/1.13              A @ A @ 
% 0.93/1.13              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.93/1.13              ( k6_partfun1 @ A ) ) & 
% 0.93/1.13            ( r2_relset_1 @
% 0.93/1.13              A @ A @ 
% 0.93/1.13              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.93/1.13              ( k6_partfun1 @ A ) ) ) ) )),
% 0.93/1.13    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.93/1.13  thf('1', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(dt_k2_funct_2, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.93/1.13         ( v3_funct_2 @ B @ A @ A ) & 
% 0.93/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.93/1.13       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.93/1.13         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.93/1.13         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.93/1.13         ( m1_subset_1 @
% 0.93/1.13           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.93/1.13  thf('2', plain,
% 0.93/1.13      (![X17 : $i, X18 : $i]:
% 0.93/1.13         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 0.93/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.93/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.93/1.13          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.93/1.13          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.93/1.13          | ~ (v1_funct_1 @ X18))),
% 0.93/1.13      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.93/1.13  thf('3', plain,
% 0.93/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.93/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['1', '2'])).
% 0.93/1.13  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('7', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(redefinition_k2_funct_2, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.93/1.13         ( v3_funct_2 @ B @ A @ A ) & 
% 0.93/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.93/1.13       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.93/1.13  thf('8', plain,
% 0.93/1.13      (![X27 : $i, X28 : $i]:
% 0.93/1.13         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 0.93/1.13          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.93/1.13          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 0.93/1.13          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 0.93/1.13          | ~ (v1_funct_1 @ X27))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.93/1.13  thf('9', plain,
% 0.93/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['7', '8'])).
% 0.93/1.13  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('11', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('12', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('13', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.93/1.13  thf('14', plain,
% 0.93/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.93/1.13  thf('15', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(redefinition_k1_partfun1, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.93/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.93/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.93/1.13         ( v1_funct_1 @ F ) & 
% 0.93/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.93/1.13       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.93/1.13  thf('16', plain,
% 0.93/1.13      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.93/1.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.93/1.13          | ~ (v1_funct_1 @ X21)
% 0.93/1.13          | ~ (v1_funct_1 @ X24)
% 0.93/1.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.93/1.13          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.93/1.13              = (k5_relat_1 @ X21 @ X24)))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.93/1.13  thf('17', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.93/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.93/1.13            = (k5_relat_1 @ sk_B @ X0))
% 0.93/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.93/1.13          | ~ (v1_funct_1 @ X0)
% 0.93/1.13          | ~ (v1_funct_1 @ sk_B))),
% 0.93/1.13      inference('sup-', [status(thm)], ['15', '16'])).
% 0.93/1.13  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('19', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.93/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.93/1.13            = (k5_relat_1 @ sk_B @ X0))
% 0.93/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.93/1.13          | ~ (v1_funct_1 @ X0))),
% 0.93/1.13      inference('demod', [status(thm)], ['17', '18'])).
% 0.93/1.13  thf('20', plain,
% 0.93/1.13      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.93/1.13        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['14', '19'])).
% 0.93/1.13  thf('21', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('22', plain,
% 0.93/1.13      (![X17 : $i, X18 : $i]:
% 0.93/1.13         ((v1_funct_1 @ (k2_funct_2 @ X17 @ X18))
% 0.93/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.93/1.13          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.93/1.13          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.93/1.13          | ~ (v1_funct_1 @ X18))),
% 0.93/1.13      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.93/1.13  thf('23', plain,
% 0.93/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['21', '22'])).
% 0.93/1.13  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('25', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('26', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('27', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.93/1.13  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.93/1.13  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['27', '28'])).
% 0.93/1.13  thf('30', plain,
% 0.93/1.13      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.93/1.13         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.93/1.13      inference('demod', [status(thm)], ['20', '29'])).
% 0.93/1.13  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.93/1.13  thf('32', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13           (k6_partfun1 @ sk_A))
% 0.93/1.13        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13             (k6_partfun1 @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(redefinition_k6_partfun1, axiom,
% 0.93/1.13    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.93/1.13  thf('33', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.93/1.13  thf('34', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.93/1.13  thf('35', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13           (k6_relat_1 @ sk_A))
% 0.93/1.13        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13             (k6_relat_1 @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.93/1.13  thf('36', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13           (k6_relat_1 @ sk_A)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('split', [status(esa)], ['35'])).
% 0.93/1.13  thf('37', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13            (k2_funct_1 @ sk_B)) @ 
% 0.93/1.13           (k6_relat_1 @ sk_A)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['31', '36'])).
% 0.93/1.13  thf('38', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['30', '37'])).
% 0.93/1.13  thf('39', plain,
% 0.93/1.13      (![X1 : $i]:
% 0.93/1.13         (~ (v2_funct_1 @ X1)
% 0.93/1.13          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.93/1.13              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.93/1.13          | ~ (v1_funct_1 @ X1)
% 0.93/1.13          | ~ (v1_relat_1 @ X1))),
% 0.93/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.93/1.13  thf('40', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('41', plain,
% 0.93/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.93/1.13  thf('42', plain,
% 0.93/1.13      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.93/1.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.93/1.13          | ~ (v1_funct_1 @ X21)
% 0.93/1.13          | ~ (v1_funct_1 @ X24)
% 0.93/1.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.93/1.13          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.93/1.13              = (k5_relat_1 @ X21 @ X24)))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.93/1.13  thf('43', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.93/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.93/1.13            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.93/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.93/1.13          | ~ (v1_funct_1 @ X0)
% 0.93/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['41', '42'])).
% 0.93/1.13  thf('44', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['27', '28'])).
% 0.93/1.13  thf('45', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.93/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.93/1.13            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.93/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.93/1.13          | ~ (v1_funct_1 @ X0))),
% 0.93/1.13      inference('demod', [status(thm)], ['43', '44'])).
% 0.93/1.13  thf('46', plain,
% 0.93/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['40', '45'])).
% 0.93/1.13  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('48', plain,
% 0.93/1.13      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.93/1.13         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['46', '47'])).
% 0.93/1.13  thf('49', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.93/1.13  thf('50', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13           (k6_relat_1 @ sk_A)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('split', [status(esa)], ['35'])).
% 0.93/1.13  thf('51', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13            sk_B) @ 
% 0.93/1.13           (k6_relat_1 @ sk_A)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['49', '50'])).
% 0.93/1.13  thf('52', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['48', '51'])).
% 0.93/1.13  thf('53', plain,
% 0.93/1.13      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.93/1.13            (k6_relat_1 @ sk_A))
% 0.93/1.13         | ~ (v1_relat_1 @ sk_B)
% 0.93/1.13         | ~ (v1_funct_1 @ sk_B)
% 0.93/1.13         | ~ (v2_funct_1 @ sk_B)))
% 0.93/1.13         <= (~
% 0.93/1.13             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13               (k6_relat_1 @ sk_A))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['39', '52'])).
% 0.93/1.13  thf('54', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(cc2_funct_2, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i]:
% 0.93/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.93/1.13       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.93/1.13         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.93/1.13  thf('55', plain,
% 0.93/1.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.93/1.13         (~ (v1_funct_1 @ X12)
% 0.93/1.13          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 0.93/1.13          | (v2_funct_2 @ X12 @ X14)
% 0.93/1.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.93/1.13  thf('56', plain,
% 0.93/1.13      (((v2_funct_2 @ sk_B @ sk_A)
% 0.93/1.13        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v1_funct_1 @ sk_B))),
% 0.93/1.13      inference('sup-', [status(thm)], ['54', '55'])).
% 0.93/1.13  thf('57', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('59', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.93/1.13      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.93/1.13  thf(d3_funct_2, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.93/1.13       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.93/1.13  thf('60', plain,
% 0.93/1.13      (![X15 : $i, X16 : $i]:
% 0.93/1.13         (~ (v2_funct_2 @ X16 @ X15)
% 0.93/1.13          | ((k2_relat_1 @ X16) = (X15))
% 0.93/1.13          | ~ (v5_relat_1 @ X16 @ X15)
% 0.93/1.13          | ~ (v1_relat_1 @ X16))),
% 0.93/1.13      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.93/1.13  thf('61', plain,
% 0.93/1.13      ((~ (v1_relat_1 @ sk_B)
% 0.93/1.13        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.93/1.13        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['59', '60'])).
% 0.93/1.13  thf('62', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(cc1_relset_1, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i]:
% 0.93/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.93/1.13       ( v1_relat_1 @ C ) ))).
% 0.93/1.13  thf('63', plain,
% 0.93/1.13      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.93/1.13         ((v1_relat_1 @ X2)
% 0.93/1.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.93/1.13  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.93/1.13      inference('sup-', [status(thm)], ['62', '63'])).
% 0.93/1.13  thf('65', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(cc2_relset_1, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i]:
% 0.93/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.93/1.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.93/1.13  thf('66', plain,
% 0.93/1.13      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.93/1.13         ((v5_relat_1 @ X5 @ X7)
% 0.93/1.13          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.93/1.13  thf('67', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.93/1.13      inference('sup-', [status(thm)], ['65', '66'])).
% 0.93/1.13  thf('68', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.93/1.13      inference('demod', [status(thm)], ['61', '64', '67'])).
% 0.93/1.13  thf(dt_k6_partfun1, axiom,
% 0.93/1.13    (![A:$i]:
% 0.93/1.13     ( ( m1_subset_1 @
% 0.93/1.13         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.93/1.13       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.93/1.13  thf('69', plain,
% 0.93/1.13      (![X20 : $i]:
% 0.93/1.13         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 0.93/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.93/1.13      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.93/1.13  thf('70', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.93/1.13  thf('71', plain,
% 0.93/1.13      (![X20 : $i]:
% 0.93/1.13         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 0.93/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.93/1.13      inference('demod', [status(thm)], ['69', '70'])).
% 0.93/1.13  thf(redefinition_r2_relset_1, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.93/1.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.93/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.93/1.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.93/1.13  thf('72', plain,
% 0.93/1.13      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.93/1.13         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.93/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.93/1.13          | (r2_relset_1 @ X9 @ X10 @ X8 @ X11)
% 0.93/1.13          | ((X8) != (X11)))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.93/1.13  thf('73', plain,
% 0.93/1.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.93/1.13         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 0.93/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.93/1.13      inference('simplify', [status(thm)], ['72'])).
% 0.93/1.13  thf('74', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['71', '73'])).
% 0.93/1.13  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.93/1.13      inference('sup-', [status(thm)], ['62', '63'])).
% 0.93/1.13  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('77', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('78', plain,
% 0.93/1.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.93/1.13         (~ (v1_funct_1 @ X12)
% 0.93/1.13          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 0.93/1.13          | (v2_funct_1 @ X12)
% 0.93/1.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.93/1.13  thf('79', plain,
% 0.93/1.13      (((v2_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v1_funct_1 @ sk_B))),
% 0.93/1.13      inference('sup-', [status(thm)], ['77', '78'])).
% 0.93/1.13  thf('80', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('82', plain, ((v2_funct_1 @ sk_B)),
% 0.93/1.13      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.93/1.13  thf('83', plain,
% 0.93/1.13      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13         (k6_relat_1 @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['53', '68', '74', '75', '76', '82'])).
% 0.93/1.13  thf('84', plain,
% 0.93/1.13      (~
% 0.93/1.13       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13         (k6_relat_1 @ sk_A))) | 
% 0.93/1.13       ~
% 0.93/1.13       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.93/1.13          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.93/1.13         (k6_relat_1 @ sk_A)))),
% 0.93/1.13      inference('split', [status(esa)], ['35'])).
% 0.93/1.13  thf('85', plain,
% 0.93/1.13      (~
% 0.93/1.13       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.93/1.13          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.93/1.13         (k6_relat_1 @ sk_A)))),
% 0.93/1.13      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.93/1.13  thf('86', plain,
% 0.93/1.13      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.93/1.13          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 0.93/1.13      inference('simpl_trail', [status(thm)], ['38', '85'])).
% 0.93/1.13  thf('87', plain,
% 0.93/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.93/1.13           (k6_relat_1 @ sk_A))
% 0.93/1.13        | ~ (v1_relat_1 @ sk_B)
% 0.93/1.13        | ~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v2_funct_1 @ sk_B))),
% 0.93/1.13      inference('sup-', [status(thm)], ['0', '86'])).
% 0.93/1.13  thf(t55_funct_1, axiom,
% 0.93/1.13    (![A:$i]:
% 0.93/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.93/1.13       ( ( v2_funct_1 @ A ) =>
% 0.93/1.13         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.93/1.13           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.93/1.13  thf('88', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (~ (v2_funct_1 @ X0)
% 0.93/1.13          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.93/1.13          | ~ (v1_funct_1 @ X0)
% 0.93/1.13          | ~ (v1_relat_1 @ X0))),
% 0.93/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.93/1.13  thf('89', plain,
% 0.93/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.93/1.13  thf('90', plain,
% 0.93/1.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.93/1.13         (~ (v1_funct_1 @ X12)
% 0.93/1.13          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 0.93/1.13          | (v2_funct_2 @ X12 @ X14)
% 0.93/1.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.93/1.13  thf('91', plain,
% 0.93/1.13      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.93/1.13        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['89', '90'])).
% 0.93/1.13  thf('92', plain,
% 0.93/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('93', plain,
% 0.93/1.13      (![X17 : $i, X18 : $i]:
% 0.93/1.13         ((v3_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 0.93/1.13          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.93/1.13          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.93/1.13          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.93/1.13          | ~ (v1_funct_1 @ X18))),
% 0.93/1.13      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.93/1.13  thf('94', plain,
% 0.93/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.93/1.13        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.93/1.13      inference('sup-', [status(thm)], ['92', '93'])).
% 0.93/1.13  thf('95', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('96', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('97', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('98', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.93/1.13  thf('99', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.93/1.13      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.93/1.13  thf('100', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('demod', [status(thm)], ['27', '28'])).
% 0.93/1.13  thf('101', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.93/1.13      inference('demod', [status(thm)], ['91', '99', '100'])).
% 0.93/1.13  thf('102', plain,
% 0.93/1.13      (![X15 : $i, X16 : $i]:
% 0.93/1.13         (~ (v2_funct_2 @ X16 @ X15)
% 0.93/1.13          | ((k2_relat_1 @ X16) = (X15))
% 0.93/1.13          | ~ (v5_relat_1 @ X16 @ X15)
% 0.93/1.13          | ~ (v1_relat_1 @ X16))),
% 0.93/1.13      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.93/1.13  thf('103', plain,
% 0.93/1.13      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.93/1.13        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.93/1.13        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['101', '102'])).
% 0.93/1.13  thf('104', plain,
% 0.93/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.93/1.13  thf('105', plain,
% 0.93/1.13      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.93/1.13         ((v1_relat_1 @ X2)
% 0.93/1.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.93/1.13  thf('106', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.93/1.13      inference('sup-', [status(thm)], ['104', '105'])).
% 0.93/1.13  thf('107', plain,
% 0.93/1.13      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.93/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.93/1.13      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.93/1.13  thf('108', plain,
% 0.93/1.13      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.93/1.13         ((v5_relat_1 @ X5 @ X7)
% 0.93/1.13          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.93/1.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.93/1.13  thf('109', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.93/1.13      inference('sup-', [status(thm)], ['107', '108'])).
% 0.93/1.13  thf('110', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.93/1.13      inference('demod', [status(thm)], ['103', '106', '109'])).
% 0.93/1.13  thf('111', plain,
% 0.93/1.13      ((((k1_relat_1 @ sk_B) = (sk_A))
% 0.93/1.13        | ~ (v1_relat_1 @ sk_B)
% 0.93/1.13        | ~ (v1_funct_1 @ sk_B)
% 0.93/1.13        | ~ (v2_funct_1 @ sk_B))),
% 0.93/1.13      inference('sup+', [status(thm)], ['88', '110'])).
% 0.93/1.13  thf('112', plain, ((v1_relat_1 @ sk_B)),
% 0.93/1.13      inference('sup-', [status(thm)], ['62', '63'])).
% 0.93/1.13  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('114', plain, ((v2_funct_1 @ sk_B)),
% 0.93/1.13      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.93/1.13  thf('115', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.93/1.13      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.93/1.13  thf('116', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['71', '73'])).
% 0.93/1.13  thf('117', plain, ((v1_relat_1 @ sk_B)),
% 0.93/1.13      inference('sup-', [status(thm)], ['62', '63'])).
% 0.93/1.13  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('119', plain, ((v2_funct_1 @ sk_B)),
% 0.93/1.13      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.93/1.13  thf('120', plain, ($false),
% 0.93/1.13      inference('demod', [status(thm)],
% 0.93/1.13                ['87', '115', '116', '117', '118', '119'])).
% 0.93/1.13  
% 0.93/1.13  % SZS output end Refutation
% 0.93/1.13  
% 0.93/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
