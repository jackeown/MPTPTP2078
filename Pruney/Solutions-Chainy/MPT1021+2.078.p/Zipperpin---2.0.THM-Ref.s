%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BR2IWnRAiz

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:23 EST 2020

% Result     : Theorem 7.96s
% Output     : Refutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 703 expanded)
%              Number of leaves         :   36 ( 229 expanded)
%              Depth                    :   20
%              Number of atoms          : 1744 (15003 expanded)
%              Number of equality atoms :   54 ( 116 expanded)
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

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('38',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('54',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('56',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('57',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('70',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','67','68','69'])).

thf('71',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( X9 = X12 )
      | ~ ( r2_relset_1 @ X10 @ X11 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('76',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','67','68','69'])).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( r2_relset_1 @ X10 @ X11 @ X9 @ X12 )
      | ( X9 != X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('78',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('85',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('87',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','86'])).

thf('88',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('93',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('100',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('109',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','111'])).

thf('113',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','112'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('115',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('116',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('117',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('126',plain,(
    v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['117','124','125'])).

thf('127',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('133',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('135',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('136',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['128','133','136'])).

thf('138',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('139',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('142',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('146',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('147',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['113','144','145','146','147','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BR2IWnRAiz
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.96/8.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.96/8.14  % Solved by: fo/fo7.sh
% 7.96/8.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.96/8.14  % done 6384 iterations in 7.684s
% 7.96/8.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.96/8.14  % SZS output start Refutation
% 7.96/8.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.96/8.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.96/8.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.96/8.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 7.96/8.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.96/8.14  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 7.96/8.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.96/8.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.96/8.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.96/8.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.96/8.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 7.96/8.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.96/8.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 7.96/8.14  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 7.96/8.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 7.96/8.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.96/8.14  thf(sk_A_type, type, sk_A: $i).
% 7.96/8.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 7.96/8.14  thf(sk_B_type, type, sk_B: $i).
% 7.96/8.14  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 7.96/8.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 7.96/8.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 7.96/8.14  thf(t61_funct_1, axiom,
% 7.96/8.14    (![A:$i]:
% 7.96/8.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.96/8.14       ( ( v2_funct_1 @ A ) =>
% 7.96/8.14         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 7.96/8.14             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 7.96/8.14           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 7.96/8.14             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 7.96/8.14  thf('0', plain,
% 7.96/8.14      (![X5 : $i]:
% 7.96/8.14         (~ (v2_funct_1 @ X5)
% 7.96/8.14          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 7.96/8.14              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 7.96/8.14          | ~ (v1_funct_1 @ X5)
% 7.96/8.14          | ~ (v1_relat_1 @ X5))),
% 7.96/8.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 7.96/8.14  thf(redefinition_k6_partfun1, axiom,
% 7.96/8.14    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 7.96/8.14  thf('1', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.96/8.14  thf('2', plain,
% 7.96/8.14      (![X5 : $i]:
% 7.96/8.14         (~ (v2_funct_1 @ X5)
% 7.96/8.14          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 7.96/8.14              = (k6_partfun1 @ (k1_relat_1 @ X5)))
% 7.96/8.14          | ~ (v1_funct_1 @ X5)
% 7.96/8.14          | ~ (v1_relat_1 @ X5))),
% 7.96/8.14      inference('demod', [status(thm)], ['0', '1'])).
% 7.96/8.14  thf(t88_funct_2, conjecture,
% 7.96/8.14    (![A:$i,B:$i]:
% 7.96/8.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.96/8.14         ( v3_funct_2 @ B @ A @ A ) & 
% 7.96/8.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.96/8.14       ( ( r2_relset_1 @
% 7.96/8.14           A @ A @ 
% 7.96/8.14           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 7.96/8.14           ( k6_partfun1 @ A ) ) & 
% 7.96/8.14         ( r2_relset_1 @
% 7.96/8.14           A @ A @ 
% 7.96/8.14           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 7.96/8.14           ( k6_partfun1 @ A ) ) ) ))).
% 7.96/8.14  thf(zf_stmt_0, negated_conjecture,
% 7.96/8.14    (~( ![A:$i,B:$i]:
% 7.96/8.14        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.96/8.14            ( v3_funct_2 @ B @ A @ A ) & 
% 7.96/8.14            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.96/8.14          ( ( r2_relset_1 @
% 7.96/8.14              A @ A @ 
% 7.96/8.14              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 7.96/8.14              ( k6_partfun1 @ A ) ) & 
% 7.96/8.14            ( r2_relset_1 @
% 7.96/8.14              A @ A @ 
% 7.96/8.14              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 7.96/8.14              ( k6_partfun1 @ A ) ) ) ) )),
% 7.96/8.14    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 7.96/8.14  thf('3', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A))
% 7.96/8.14        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14             (k6_partfun1 @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('4', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A)))
% 7.96/8.14         <= (~
% 7.96/8.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.96/8.14               (k6_partfun1 @ sk_A))))),
% 7.96/8.14      inference('split', [status(esa)], ['3'])).
% 7.96/8.14  thf('5', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf(redefinition_k2_funct_2, axiom,
% 7.96/8.14    (![A:$i,B:$i]:
% 7.96/8.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.96/8.14         ( v3_funct_2 @ B @ A @ A ) & 
% 7.96/8.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.96/8.14       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 7.96/8.14  thf('6', plain,
% 7.96/8.14      (![X27 : $i, X28 : $i]:
% 7.96/8.14         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 7.96/8.14          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 7.96/8.14          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 7.96/8.14          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 7.96/8.14          | ~ (v1_funct_1 @ X27))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 7.96/8.14  thf('7', plain,
% 7.96/8.14      ((~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['5', '6'])).
% 7.96/8.14  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('12', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14            (k2_funct_1 @ sk_B)) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A)))
% 7.96/8.14         <= (~
% 7.96/8.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.96/8.14               (k6_partfun1 @ sk_A))))),
% 7.96/8.14      inference('demod', [status(thm)], ['4', '11'])).
% 7.96/8.14  thf('13', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('14', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf(dt_k2_funct_2, axiom,
% 7.96/8.14    (![A:$i,B:$i]:
% 7.96/8.14     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.96/8.14         ( v3_funct_2 @ B @ A @ A ) & 
% 7.96/8.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.96/8.14       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 7.96/8.14         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 7.96/8.14         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 7.96/8.14         ( m1_subset_1 @
% 7.96/8.14           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 7.96/8.14  thf('15', plain,
% 7.96/8.14      (![X19 : $i, X20 : $i]:
% 7.96/8.14         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 7.96/8.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 7.96/8.14          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 7.96/8.14          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 7.96/8.14          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 7.96/8.14          | ~ (v1_funct_1 @ X20))),
% 7.96/8.14      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 7.96/8.14  thf('16', plain,
% 7.96/8.14      ((~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 7.96/8.14      inference('sup-', [status(thm)], ['14', '15'])).
% 7.96/8.14  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('20', plain,
% 7.96/8.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 7.96/8.14  thf(redefinition_k1_partfun1, axiom,
% 7.96/8.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.96/8.14     ( ( ( v1_funct_1 @ E ) & 
% 7.96/8.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.96/8.14         ( v1_funct_1 @ F ) & 
% 7.96/8.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 7.96/8.14       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 7.96/8.14  thf('21', plain,
% 7.96/8.14      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 7.96/8.14         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 7.96/8.14          | ~ (v1_funct_1 @ X21)
% 7.96/8.14          | ~ (v1_funct_1 @ X24)
% 7.96/8.14          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 7.96/8.14          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 7.96/8.14              = (k5_relat_1 @ X21 @ X24)))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 7.96/8.14  thf('22', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.96/8.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 7.96/8.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.96/8.14          | ~ (v1_funct_1 @ X0)
% 7.96/8.14          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['20', '21'])).
% 7.96/8.14  thf('23', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('24', plain,
% 7.96/8.14      (![X19 : $i, X20 : $i]:
% 7.96/8.14         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 7.96/8.14          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 7.96/8.14          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 7.96/8.14          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 7.96/8.14          | ~ (v1_funct_1 @ X20))),
% 7.96/8.14      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 7.96/8.14  thf('25', plain,
% 7.96/8.14      ((~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['23', '24'])).
% 7.96/8.14  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 7.96/8.14  thf('30', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.96/8.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 7.96/8.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.96/8.14          | ~ (v1_funct_1 @ X0))),
% 7.96/8.14      inference('demod', [status(thm)], ['22', '29'])).
% 7.96/8.14  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('33', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.96/8.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 7.96/8.14            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 7.96/8.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.96/8.14          | ~ (v1_funct_1 @ X0))),
% 7.96/8.14      inference('demod', [status(thm)], ['30', '31', '32'])).
% 7.96/8.14  thf('34', plain,
% 7.96/8.14      ((~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 7.96/8.14            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['13', '33'])).
% 7.96/8.14  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('36', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf(cc2_funct_2, axiom,
% 7.96/8.14    (![A:$i,B:$i,C:$i]:
% 7.96/8.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.96/8.14       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 7.96/8.14         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 7.96/8.14  thf('37', plain,
% 7.96/8.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.96/8.14         (~ (v1_funct_1 @ X14)
% 7.96/8.14          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 7.96/8.14          | (v2_funct_2 @ X14 @ X16)
% 7.96/8.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_funct_2])).
% 7.96/8.14  thf('38', plain,
% 7.96/8.14      (((v2_funct_2 @ sk_B @ sk_A)
% 7.96/8.14        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v1_funct_1 @ sk_B))),
% 7.96/8.14      inference('sup-', [status(thm)], ['36', '37'])).
% 7.96/8.14  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 7.96/8.14      inference('demod', [status(thm)], ['38', '39', '40'])).
% 7.96/8.14  thf(d3_funct_2, axiom,
% 7.96/8.14    (![A:$i,B:$i]:
% 7.96/8.14     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 7.96/8.14       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 7.96/8.14  thf('42', plain,
% 7.96/8.14      (![X17 : $i, X18 : $i]:
% 7.96/8.14         (~ (v2_funct_2 @ X18 @ X17)
% 7.96/8.14          | ((k2_relat_1 @ X18) = (X17))
% 7.96/8.14          | ~ (v5_relat_1 @ X18 @ X17)
% 7.96/8.14          | ~ (v1_relat_1 @ X18))),
% 7.96/8.14      inference('cnf', [status(esa)], [d3_funct_2])).
% 7.96/8.14  thf('43', plain,
% 7.96/8.14      ((~ (v1_relat_1 @ sk_B)
% 7.96/8.14        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 7.96/8.14        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['41', '42'])).
% 7.96/8.14  thf('44', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf(cc2_relat_1, axiom,
% 7.96/8.14    (![A:$i]:
% 7.96/8.14     ( ( v1_relat_1 @ A ) =>
% 7.96/8.14       ( ![B:$i]:
% 7.96/8.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 7.96/8.14  thf('45', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i]:
% 7.96/8.14         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 7.96/8.14          | (v1_relat_1 @ X0)
% 7.96/8.14          | ~ (v1_relat_1 @ X1))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.96/8.14  thf('46', plain,
% 7.96/8.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 7.96/8.14      inference('sup-', [status(thm)], ['44', '45'])).
% 7.96/8.14  thf(fc6_relat_1, axiom,
% 7.96/8.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 7.96/8.14  thf('47', plain,
% 7.96/8.14      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 7.96/8.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.96/8.14  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['46', '47'])).
% 7.96/8.14  thf('49', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf(cc2_relset_1, axiom,
% 7.96/8.14    (![A:$i,B:$i,C:$i]:
% 7.96/8.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.96/8.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.96/8.14  thf('50', plain,
% 7.96/8.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 7.96/8.14         ((v5_relat_1 @ X6 @ X8)
% 7.96/8.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.96/8.14  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 7.96/8.14      inference('sup-', [status(thm)], ['49', '50'])).
% 7.96/8.14  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['43', '48', '51'])).
% 7.96/8.14  thf('53', plain,
% 7.96/8.14      (![X5 : $i]:
% 7.96/8.14         (~ (v2_funct_1 @ X5)
% 7.96/8.14          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 7.96/8.14              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 7.96/8.14          | ~ (v1_funct_1 @ X5)
% 7.96/8.14          | ~ (v1_relat_1 @ X5))),
% 7.96/8.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 7.96/8.14  thf('54', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.96/8.14  thf('55', plain,
% 7.96/8.14      (![X5 : $i]:
% 7.96/8.14         (~ (v2_funct_1 @ X5)
% 7.96/8.14          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 7.96/8.14              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 7.96/8.14          | ~ (v1_funct_1 @ X5)
% 7.96/8.14          | ~ (v1_relat_1 @ X5))),
% 7.96/8.14      inference('demod', [status(thm)], ['53', '54'])).
% 7.96/8.14  thf(t29_relset_1, axiom,
% 7.96/8.14    (![A:$i]:
% 7.96/8.14     ( m1_subset_1 @
% 7.96/8.14       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 7.96/8.14  thf('56', plain,
% 7.96/8.14      (![X13 : $i]:
% 7.96/8.14         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 7.96/8.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 7.96/8.14      inference('cnf', [status(esa)], [t29_relset_1])).
% 7.96/8.14  thf('57', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.96/8.14  thf('58', plain,
% 7.96/8.14      (![X13 : $i]:
% 7.96/8.14         (m1_subset_1 @ (k6_partfun1 @ X13) @ 
% 7.96/8.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 7.96/8.14      inference('demod', [status(thm)], ['56', '57'])).
% 7.96/8.14  thf('59', plain,
% 7.96/8.14      (![X0 : $i]:
% 7.96/8.14         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 7.96/8.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 7.96/8.14          | ~ (v1_relat_1 @ X0)
% 7.96/8.14          | ~ (v1_funct_1 @ X0)
% 7.96/8.14          | ~ (v2_funct_1 @ X0))),
% 7.96/8.14      inference('sup+', [status(thm)], ['55', '58'])).
% 7.96/8.14  thf('60', plain,
% 7.96/8.14      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 7.96/8.14         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 7.96/8.14        | ~ (v2_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v1_relat_1 @ sk_B))),
% 7.96/8.14      inference('sup+', [status(thm)], ['52', '59'])).
% 7.96/8.14  thf('61', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['43', '48', '51'])).
% 7.96/8.14  thf('62', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('63', plain,
% 7.96/8.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.96/8.14         (~ (v1_funct_1 @ X14)
% 7.96/8.14          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 7.96/8.14          | (v2_funct_1 @ X14)
% 7.96/8.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_funct_2])).
% 7.96/8.14  thf('64', plain,
% 7.96/8.14      (((v2_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v1_funct_1 @ sk_B))),
% 7.96/8.14      inference('sup-', [status(thm)], ['62', '63'])).
% 7.96/8.14  thf('65', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('67', plain, ((v2_funct_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['64', '65', '66'])).
% 7.96/8.14  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['46', '47'])).
% 7.96/8.14  thf('70', plain,
% 7.96/8.14      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['60', '61', '67', '68', '69'])).
% 7.96/8.14  thf('71', plain,
% 7.96/8.14      (![X13 : $i]:
% 7.96/8.14         (m1_subset_1 @ (k6_partfun1 @ X13) @ 
% 7.96/8.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 7.96/8.14      inference('demod', [status(thm)], ['56', '57'])).
% 7.96/8.14  thf(redefinition_r2_relset_1, axiom,
% 7.96/8.14    (![A:$i,B:$i,C:$i,D:$i]:
% 7.96/8.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.96/8.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.96/8.14       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 7.96/8.14  thf('72', plain,
% 7.96/8.14      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 7.96/8.14         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 7.96/8.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 7.96/8.14          | ((X9) = (X12))
% 7.96/8.14          | ~ (r2_relset_1 @ X10 @ X11 @ X9 @ X12))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 7.96/8.14  thf('73', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i]:
% 7.96/8.14         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 7.96/8.14          | ((k6_partfun1 @ X0) = (X1))
% 7.96/8.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 7.96/8.14      inference('sup-', [status(thm)], ['71', '72'])).
% 7.96/8.14  thf('74', plain,
% 7.96/8.14      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 7.96/8.14        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 7.96/8.14             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['70', '73'])).
% 7.96/8.14  thf('75', plain,
% 7.96/8.14      (![X5 : $i]:
% 7.96/8.14         (~ (v2_funct_1 @ X5)
% 7.96/8.14          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 7.96/8.14              = (k6_partfun1 @ (k2_relat_1 @ X5)))
% 7.96/8.14          | ~ (v1_funct_1 @ X5)
% 7.96/8.14          | ~ (v1_relat_1 @ X5))),
% 7.96/8.14      inference('demod', [status(thm)], ['53', '54'])).
% 7.96/8.14  thf('76', plain,
% 7.96/8.14      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['60', '61', '67', '68', '69'])).
% 7.96/8.14  thf('77', plain,
% 7.96/8.14      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 7.96/8.14         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 7.96/8.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 7.96/8.14          | (r2_relset_1 @ X10 @ X11 @ X9 @ X12)
% 7.96/8.14          | ((X9) != (X12)))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 7.96/8.14  thf('78', plain,
% 7.96/8.14      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.96/8.14         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 7.96/8.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 7.96/8.14      inference('simplify', [status(thm)], ['77'])).
% 7.96/8.14  thf('79', plain,
% 7.96/8.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 7.96/8.14        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 7.96/8.14      inference('sup-', [status(thm)], ['76', '78'])).
% 7.96/8.14  thf('80', plain,
% 7.96/8.14      (((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k2_relat_1 @ sk_B)) @ 
% 7.96/8.14         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 7.96/8.14        | ~ (v1_relat_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v2_funct_1 @ sk_B))),
% 7.96/8.14      inference('sup+', [status(thm)], ['75', '79'])).
% 7.96/8.14  thf('81', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['43', '48', '51'])).
% 7.96/8.14  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['46', '47'])).
% 7.96/8.14  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['64', '65', '66'])).
% 7.96/8.14  thf('85', plain,
% 7.96/8.14      ((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 7.96/8.14        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 7.96/8.14  thf('86', plain,
% 7.96/8.14      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['74', '85'])).
% 7.96/8.14  thf('87', plain,
% 7.96/8.14      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 7.96/8.14         = (k6_partfun1 @ sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['34', '35', '86'])).
% 7.96/8.14  thf('88', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('89', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A)))
% 7.96/8.14         <= (~
% 7.96/8.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14               (k6_partfun1 @ sk_A))))),
% 7.96/8.14      inference('split', [status(esa)], ['3'])).
% 7.96/8.14  thf('90', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 7.96/8.14            sk_B) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A)))
% 7.96/8.14         <= (~
% 7.96/8.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14               (k6_partfun1 @ sk_A))))),
% 7.96/8.14      inference('sup-', [status(thm)], ['88', '89'])).
% 7.96/8.14  thf('91', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A)))
% 7.96/8.14         <= (~
% 7.96/8.14             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14               (k6_partfun1 @ sk_A))))),
% 7.96/8.14      inference('sup-', [status(thm)], ['87', '90'])).
% 7.96/8.14  thf('92', plain,
% 7.96/8.14      (![X13 : $i]:
% 7.96/8.14         (m1_subset_1 @ (k6_partfun1 @ X13) @ 
% 7.96/8.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 7.96/8.14      inference('demod', [status(thm)], ['56', '57'])).
% 7.96/8.14  thf('93', plain,
% 7.96/8.14      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.96/8.14         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 7.96/8.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 7.96/8.14      inference('simplify', [status(thm)], ['77'])).
% 7.96/8.14  thf('94', plain,
% 7.96/8.14      (![X0 : $i]:
% 7.96/8.14         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 7.96/8.14      inference('sup-', [status(thm)], ['92', '93'])).
% 7.96/8.14  thf('95', plain,
% 7.96/8.14      (((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14         (k6_partfun1 @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['91', '94'])).
% 7.96/8.14  thf('96', plain,
% 7.96/8.14      (~
% 7.96/8.14       ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.96/8.14         (k6_partfun1 @ sk_A))) | 
% 7.96/8.14       ~
% 7.96/8.14       ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.96/8.14          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.96/8.14         (k6_partfun1 @ sk_A)))),
% 7.96/8.14      inference('split', [status(esa)], ['3'])).
% 7.96/8.14  thf('97', plain,
% 7.96/8.14      (~
% 7.96/8.14       ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.96/8.14         (k6_partfun1 @ sk_A)))),
% 7.96/8.14      inference('sat_resolution*', [status(thm)], ['95', '96'])).
% 7.96/8.14  thf('98', plain,
% 7.96/8.14      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 7.96/8.14          (k6_partfun1 @ sk_A))),
% 7.96/8.14      inference('simpl_trail', [status(thm)], ['12', '97'])).
% 7.96/8.14  thf('99', plain,
% 7.96/8.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 7.96/8.14  thf('100', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('101', plain,
% 7.96/8.14      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['99', '100'])).
% 7.96/8.14  thf('102', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('103', plain,
% 7.96/8.14      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 7.96/8.14         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 7.96/8.14          | ~ (v1_funct_1 @ X21)
% 7.96/8.14          | ~ (v1_funct_1 @ X24)
% 7.96/8.14          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 7.96/8.14          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 7.96/8.14              = (k5_relat_1 @ X21 @ X24)))),
% 7.96/8.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 7.96/8.14  thf('104', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.96/8.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 7.96/8.14            = (k5_relat_1 @ sk_B @ X0))
% 7.96/8.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.96/8.14          | ~ (v1_funct_1 @ X0)
% 7.96/8.14          | ~ (v1_funct_1 @ sk_B))),
% 7.96/8.14      inference('sup-', [status(thm)], ['102', '103'])).
% 7.96/8.14  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('106', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.96/8.14         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 7.96/8.14            = (k5_relat_1 @ sk_B @ X0))
% 7.96/8.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.96/8.14          | ~ (v1_funct_1 @ X0))),
% 7.96/8.14      inference('demod', [status(thm)], ['104', '105'])).
% 7.96/8.14  thf('107', plain,
% 7.96/8.14      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 7.96/8.14        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.96/8.14            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 7.96/8.14      inference('sup-', [status(thm)], ['101', '106'])).
% 7.96/8.14  thf('108', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 7.96/8.14  thf('109', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('110', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['108', '109'])).
% 7.96/8.14  thf('111', plain,
% 7.96/8.14      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 7.96/8.14         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 7.96/8.14      inference('demod', [status(thm)], ['107', '110'])).
% 7.96/8.14  thf('112', plain,
% 7.96/8.14      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.96/8.14          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_partfun1 @ sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['98', '111'])).
% 7.96/8.14  thf('113', plain,
% 7.96/8.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 7.96/8.14           (k6_partfun1 @ sk_A))
% 7.96/8.14        | ~ (v1_relat_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v2_funct_1 @ sk_B))),
% 7.96/8.14      inference('sup-', [status(thm)], ['2', '112'])).
% 7.96/8.14  thf(t55_funct_1, axiom,
% 7.96/8.14    (![A:$i]:
% 7.96/8.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.96/8.14       ( ( v2_funct_1 @ A ) =>
% 7.96/8.14         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 7.96/8.14           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 7.96/8.14  thf('114', plain,
% 7.96/8.14      (![X4 : $i]:
% 7.96/8.14         (~ (v2_funct_1 @ X4)
% 7.96/8.14          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 7.96/8.14          | ~ (v1_funct_1 @ X4)
% 7.96/8.14          | ~ (v1_relat_1 @ X4))),
% 7.96/8.14      inference('cnf', [status(esa)], [t55_funct_1])).
% 7.96/8.14  thf('115', plain,
% 7.96/8.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 7.96/8.14  thf('116', plain,
% 7.96/8.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.96/8.14         (~ (v1_funct_1 @ X14)
% 7.96/8.14          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 7.96/8.14          | (v2_funct_2 @ X14 @ X16)
% 7.96/8.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_funct_2])).
% 7.96/8.14  thf('117', plain,
% 7.96/8.14      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)
% 7.96/8.14        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['115', '116'])).
% 7.96/8.14  thf('118', plain,
% 7.96/8.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('119', plain,
% 7.96/8.14      (![X19 : $i, X20 : $i]:
% 7.96/8.14         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 7.96/8.14          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 7.96/8.14          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 7.96/8.14          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 7.96/8.14          | ~ (v1_funct_1 @ X20))),
% 7.96/8.14      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 7.96/8.14  thf('120', plain,
% 7.96/8.14      ((~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.96/8.14        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 7.96/8.14      inference('sup-', [status(thm)], ['118', '119'])).
% 7.96/8.14  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('122', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('123', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('124', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 7.96/8.14      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 7.96/8.14  thf('125', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 7.96/8.14  thf('126', plain, ((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 7.96/8.14      inference('demod', [status(thm)], ['117', '124', '125'])).
% 7.96/8.14  thf('127', plain,
% 7.96/8.14      (![X17 : $i, X18 : $i]:
% 7.96/8.14         (~ (v2_funct_2 @ X18 @ X17)
% 7.96/8.14          | ((k2_relat_1 @ X18) = (X17))
% 7.96/8.14          | ~ (v5_relat_1 @ X18 @ X17)
% 7.96/8.14          | ~ (v1_relat_1 @ X18))),
% 7.96/8.14      inference('cnf', [status(esa)], [d3_funct_2])).
% 7.96/8.14  thf('128', plain,
% 7.96/8.14      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))
% 7.96/8.14        | ~ (v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)
% 7.96/8.14        | ((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)) = (sk_A)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['126', '127'])).
% 7.96/8.14  thf('129', plain,
% 7.96/8.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 7.96/8.14  thf('130', plain,
% 7.96/8.14      (![X0 : $i, X1 : $i]:
% 7.96/8.14         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 7.96/8.14          | (v1_relat_1 @ X0)
% 7.96/8.14          | ~ (v1_relat_1 @ X1))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.96/8.14  thf('131', plain,
% 7.96/8.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 7.96/8.14        | (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 7.96/8.14      inference('sup-', [status(thm)], ['129', '130'])).
% 7.96/8.14  thf('132', plain,
% 7.96/8.14      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 7.96/8.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.96/8.14  thf('133', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['131', '132'])).
% 7.96/8.14  thf('134', plain,
% 7.96/8.14      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.96/8.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.96/8.14      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 7.96/8.14  thf('135', plain,
% 7.96/8.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 7.96/8.14         ((v5_relat_1 @ X6 @ X8)
% 7.96/8.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 7.96/8.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.96/8.14  thf('136', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 7.96/8.14      inference('sup-', [status(thm)], ['134', '135'])).
% 7.96/8.14  thf('137', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B)) = (sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['128', '133', '136'])).
% 7.96/8.14  thf('138', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.96/8.14      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 7.96/8.14  thf('139', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['137', '138'])).
% 7.96/8.14  thf('140', plain,
% 7.96/8.14      ((((k1_relat_1 @ sk_B) = (sk_A))
% 7.96/8.14        | ~ (v1_relat_1 @ sk_B)
% 7.96/8.14        | ~ (v1_funct_1 @ sk_B)
% 7.96/8.14        | ~ (v2_funct_1 @ sk_B))),
% 7.96/8.14      inference('sup+', [status(thm)], ['114', '139'])).
% 7.96/8.14  thf('141', plain, ((v1_relat_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['46', '47'])).
% 7.96/8.14  thf('142', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('143', plain, ((v2_funct_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['64', '65', '66'])).
% 7.96/8.14  thf('144', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 7.96/8.14      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 7.96/8.14  thf('145', plain,
% 7.96/8.14      (![X0 : $i]:
% 7.96/8.14         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 7.96/8.14      inference('sup-', [status(thm)], ['92', '93'])).
% 7.96/8.14  thf('146', plain, ((v1_relat_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['46', '47'])).
% 7.96/8.14  thf('147', plain, ((v1_funct_1 @ sk_B)),
% 7.96/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.96/8.14  thf('148', plain, ((v2_funct_1 @ sk_B)),
% 7.96/8.14      inference('demod', [status(thm)], ['64', '65', '66'])).
% 7.96/8.14  thf('149', plain, ($false),
% 7.96/8.14      inference('demod', [status(thm)],
% 7.96/8.14                ['113', '144', '145', '146', '147', '148'])).
% 7.96/8.14  
% 7.96/8.14  % SZS output end Refutation
% 7.96/8.14  
% 7.96/8.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
