%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jBZP5CNQiB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:24 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  237 (2316 expanded)
%              Number of leaves         :   36 ( 724 expanded)
%              Depth                    :   18
%              Number of atoms          : 2515 (57499 expanded)
%              Number of equality atoms :   67 ( 349 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( ( k2_funct_2 @ X27 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_2 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_2 @ X17 @ X16 )
      | ( ( k2_relat_1 @ X17 )
        = X16 )
      | ~ ( v5_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('54',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('66',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','63','64','65'])).

thf('67',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('73',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 )
      | ( X8 != X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('75',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('80',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','76','77','78','79'])).

thf('81',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','80'])).

thf('82',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('83',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('89',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 )
        = ( k5_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('101',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','101'])).

thf('103',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('105',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_2 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('106',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('114',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('116',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['106','114','115'])).

thf('117',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_2 @ X17 @ X16 )
      | ( ( k2_relat_1 @ X17 )
        = X16 )
      | ~ ( v5_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('121',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('123',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('125',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('126',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['118','123','126'])).

thf('128',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('130',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) )
      | ~ ( r2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['118','123','126'])).

thf('136',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['118','123','126'])).

thf('137',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['118','123','126'])).

thf('138',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['118','123','126'])).

thf('139',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('140',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('141',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('142',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('143',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('145',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('146',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139','140','146'])).

thf('148',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('150',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('152',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('163',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('165',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154','163','164'])).

thf('166',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('167',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_funct_2 @ X27 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('168',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('170',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('171',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('172',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['165','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( sk_B
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','80'])).

thf('179',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf('180',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ( r2_relset_1 @ X30 @ X30 @ X29 @ ( k2_funct_2 @ X30 @ X31 ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X29 ) @ ( k6_partfun1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t87_funct_2])).

thf('181',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('182',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ( r2_relset_1 @ X30 @ X30 @ X29 @ ( k2_funct_2 @ X30 @ X31 ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X29 ) @ ( k6_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v3_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ X0 ) )
      | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v3_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('188',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('190',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('191',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('192',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('193',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('194',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('195',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192','193','194'])).

thf('196',plain,
    ( sk_B
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','195'])).

thf('197',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['150','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('199',plain,(
    $false ),
    inference(demod,[status(thm)],['102','197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jBZP5CNQiB
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.03/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.20  % Solved by: fo/fo7.sh
% 1.03/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.20  % done 767 iterations in 0.758s
% 1.03/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.20  % SZS output start Refutation
% 1.03/1.20  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.03/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.20  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.03/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.03/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.03/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.20  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.03/1.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.20  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.03/1.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.03/1.20  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.03/1.20  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.03/1.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.03/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.20  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.03/1.20  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.03/1.20  thf(t88_funct_2, conjecture,
% 1.03/1.20    (![A:$i,B:$i]:
% 1.03/1.20     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.03/1.20         ( v3_funct_2 @ B @ A @ A ) & 
% 1.03/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.03/1.20       ( ( r2_relset_1 @
% 1.03/1.20           A @ A @ 
% 1.03/1.20           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.03/1.20           ( k6_partfun1 @ A ) ) & 
% 1.03/1.20         ( r2_relset_1 @
% 1.03/1.20           A @ A @ 
% 1.03/1.20           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.03/1.20           ( k6_partfun1 @ A ) ) ) ))).
% 1.03/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.20    (~( ![A:$i,B:$i]:
% 1.03/1.20        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.03/1.20            ( v3_funct_2 @ B @ A @ A ) & 
% 1.03/1.20            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.03/1.20          ( ( r2_relset_1 @
% 1.03/1.20              A @ A @ 
% 1.03/1.20              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.03/1.20              ( k6_partfun1 @ A ) ) & 
% 1.03/1.20            ( r2_relset_1 @
% 1.03/1.20              A @ A @ 
% 1.03/1.20              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.03/1.20              ( k6_partfun1 @ A ) ) ) ) )),
% 1.03/1.20    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.03/1.20  thf('0', plain,
% 1.03/1.20      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.20           (k6_partfun1 @ sk_A))
% 1.03/1.20        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.20              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.20             (k6_partfun1 @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('1', plain,
% 1.03/1.20      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.20           (k6_partfun1 @ sk_A)))
% 1.03/1.20         <= (~
% 1.03/1.20             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.20               (k6_partfun1 @ sk_A))))),
% 1.03/1.20      inference('split', [status(esa)], ['0'])).
% 1.03/1.20  thf(redefinition_k6_partfun1, axiom,
% 1.03/1.20    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.03/1.20  thf('2', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.03/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.20  thf('3', plain,
% 1.03/1.20      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.20           (k6_relat_1 @ sk_A)))
% 1.03/1.20         <= (~
% 1.03/1.20             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.20               (k6_partfun1 @ sk_A))))),
% 1.03/1.20      inference('demod', [status(thm)], ['1', '2'])).
% 1.03/1.20  thf('4', plain,
% 1.03/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf(redefinition_k2_funct_2, axiom,
% 1.03/1.20    (![A:$i,B:$i]:
% 1.03/1.20     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.03/1.20         ( v3_funct_2 @ B @ A @ A ) & 
% 1.03/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.03/1.20       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.03/1.20  thf('5', plain,
% 1.03/1.20      (![X26 : $i, X27 : $i]:
% 1.03/1.20         (((k2_funct_2 @ X27 @ X26) = (k2_funct_1 @ X26))
% 1.03/1.20          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 1.03/1.20          | ~ (v3_funct_2 @ X26 @ X27 @ X27)
% 1.03/1.20          | ~ (v1_funct_2 @ X26 @ X27 @ X27)
% 1.03/1.20          | ~ (v1_funct_1 @ X26))),
% 1.03/1.20      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.03/1.20  thf('6', plain,
% 1.03/1.20      ((~ (v1_funct_1 @ sk_B)
% 1.03/1.20        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.03/1.20      inference('sup-', [status(thm)], ['4', '5'])).
% 1.03/1.20  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.03/1.20      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 1.03/1.20  thf('11', plain,
% 1.03/1.20      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20            (k2_funct_1 @ sk_B)) @ 
% 1.03/1.20           (k6_relat_1 @ sk_A)))
% 1.03/1.20         <= (~
% 1.03/1.20             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.20               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.20                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.20               (k6_partfun1 @ sk_A))))),
% 1.03/1.20      inference('demod', [status(thm)], ['3', '10'])).
% 1.03/1.20  thf('12', plain,
% 1.03/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('13', plain,
% 1.03/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf(dt_k2_funct_2, axiom,
% 1.03/1.20    (![A:$i,B:$i]:
% 1.03/1.20     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.03/1.20         ( v3_funct_2 @ B @ A @ A ) & 
% 1.03/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.03/1.20       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.03/1.20         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.03/1.20         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.03/1.20         ( m1_subset_1 @
% 1.03/1.20           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.03/1.20  thf('14', plain,
% 1.03/1.20      (![X18 : $i, X19 : $i]:
% 1.03/1.20         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 1.03/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.20          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.20          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.20          | ~ (v1_funct_1 @ X19))),
% 1.03/1.20      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.03/1.20  thf('15', plain,
% 1.03/1.20      ((~ (v1_funct_1 @ sk_B)
% 1.03/1.20        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.03/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.03/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.03/1.20  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.03/1.20      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 1.03/1.20  thf('20', plain,
% 1.03/1.20      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.20  thf(redefinition_k1_partfun1, axiom,
% 1.03/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.03/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.20         ( v1_funct_1 @ F ) & 
% 1.03/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.03/1.20       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.03/1.20  thf('21', plain,
% 1.03/1.20      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.03/1.20         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.03/1.20          | ~ (v1_funct_1 @ X20)
% 1.03/1.20          | ~ (v1_funct_1 @ X23)
% 1.03/1.20          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.03/1.20          | ((k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 1.03/1.20              = (k5_relat_1 @ X20 @ X23)))),
% 1.03/1.20      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.03/1.20  thf('22', plain,
% 1.03/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.20         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.03/1.20            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.03/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.20          | ~ (v1_funct_1 @ X0)
% 1.03/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.20      inference('sup-', [status(thm)], ['20', '21'])).
% 1.03/1.20  thf('23', plain,
% 1.03/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('24', plain,
% 1.03/1.20      (![X18 : $i, X19 : $i]:
% 1.03/1.20         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 1.03/1.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.20          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.20          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.20          | ~ (v1_funct_1 @ X19))),
% 1.03/1.20      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.03/1.20  thf('25', plain,
% 1.03/1.20      ((~ (v1_funct_1 @ sk_B)
% 1.03/1.20        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.03/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.03/1.20  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.03/1.20      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 1.03/1.20  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.03/1.20      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 1.03/1.20  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.20      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.20  thf('32', plain,
% 1.03/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.20         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.03/1.20            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.03/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.20          | ~ (v1_funct_1 @ X0))),
% 1.03/1.20      inference('demod', [status(thm)], ['22', '31'])).
% 1.03/1.20  thf('33', plain,
% 1.03/1.20      ((~ (v1_funct_1 @ sk_B)
% 1.03/1.20        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.20            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.03/1.20      inference('sup-', [status(thm)], ['12', '32'])).
% 1.03/1.20  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf(t61_funct_1, axiom,
% 1.03/1.20    (![A:$i]:
% 1.03/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.20       ( ( v2_funct_1 @ A ) =>
% 1.03/1.20         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.03/1.20             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.03/1.20           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.03/1.20             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.03/1.20  thf('35', plain,
% 1.03/1.20      (![X4 : $i]:
% 1.03/1.20         (~ (v2_funct_1 @ X4)
% 1.03/1.20          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.03/1.20              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.03/1.20          | ~ (v1_funct_1 @ X4)
% 1.03/1.20          | ~ (v1_relat_1 @ X4))),
% 1.03/1.20      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.03/1.20  thf('36', plain,
% 1.03/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf(cc2_funct_2, axiom,
% 1.03/1.20    (![A:$i,B:$i,C:$i]:
% 1.03/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.20       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.03/1.20         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.03/1.20  thf('37', plain,
% 1.03/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.20         (~ (v1_funct_1 @ X13)
% 1.03/1.20          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 1.03/1.20          | (v2_funct_2 @ X13 @ X15)
% 1.03/1.20          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.03/1.20      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.03/1.20  thf('38', plain,
% 1.03/1.20      (((v2_funct_2 @ sk_B @ sk_A)
% 1.03/1.20        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.20        | ~ (v1_funct_1 @ sk_B))),
% 1.03/1.20      inference('sup-', [status(thm)], ['36', '37'])).
% 1.03/1.20  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.03/1.20      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.03/1.20  thf(d3_funct_2, axiom,
% 1.03/1.20    (![A:$i,B:$i]:
% 1.03/1.20     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.03/1.20       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.03/1.20  thf('42', plain,
% 1.03/1.20      (![X16 : $i, X17 : $i]:
% 1.03/1.20         (~ (v2_funct_2 @ X17 @ X16)
% 1.03/1.20          | ((k2_relat_1 @ X17) = (X16))
% 1.03/1.20          | ~ (v5_relat_1 @ X17 @ X16)
% 1.03/1.20          | ~ (v1_relat_1 @ X17))),
% 1.03/1.20      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.03/1.20  thf('43', plain,
% 1.03/1.20      ((~ (v1_relat_1 @ sk_B)
% 1.03/1.20        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.03/1.20        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.03/1.20      inference('sup-', [status(thm)], ['41', '42'])).
% 1.03/1.20  thf('44', plain,
% 1.03/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.20  thf(cc2_relat_1, axiom,
% 1.03/1.20    (![A:$i]:
% 1.03/1.20     ( ( v1_relat_1 @ A ) =>
% 1.03/1.20       ( ![B:$i]:
% 1.03/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.03/1.20  thf('45', plain,
% 1.03/1.20      (![X0 : $i, X1 : $i]:
% 1.03/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.03/1.20          | (v1_relat_1 @ X0)
% 1.03/1.20          | ~ (v1_relat_1 @ X1))),
% 1.03/1.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.03/1.20  thf('46', plain,
% 1.03/1.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.03/1.21      inference('sup-', [status(thm)], ['44', '45'])).
% 1.03/1.21  thf(fc6_relat_1, axiom,
% 1.03/1.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.03/1.21  thf('47', plain,
% 1.03/1.21      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.03/1.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.03/1.21  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.03/1.21      inference('demod', [status(thm)], ['46', '47'])).
% 1.03/1.21  thf('49', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(cc2_relset_1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.03/1.21  thf('50', plain,
% 1.03/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.21         ((v5_relat_1 @ X5 @ X7)
% 1.03/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.21  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.03/1.21      inference('sup-', [status(thm)], ['49', '50'])).
% 1.03/1.21  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.03/1.21  thf('53', plain,
% 1.03/1.21      (![X4 : $i]:
% 1.03/1.21         (~ (v2_funct_1 @ X4)
% 1.03/1.21          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.03/1.21              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.03/1.21          | ~ (v1_funct_1 @ X4)
% 1.03/1.21          | ~ (v1_relat_1 @ X4))),
% 1.03/1.21      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.03/1.21  thf(t29_relset_1, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( m1_subset_1 @
% 1.03/1.21       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.03/1.21  thf('54', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         (m1_subset_1 @ (k6_relat_1 @ X12) @ 
% 1.03/1.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 1.03/1.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.03/1.21  thf('55', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v2_funct_1 @ X0))),
% 1.03/1.21      inference('sup+', [status(thm)], ['53', '54'])).
% 1.03/1.21  thf('56', plain,
% 1.03/1.21      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.03/1.21         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 1.03/1.21        | ~ (v2_funct_1 @ sk_B)
% 1.03/1.21        | ~ (v1_funct_1 @ sk_B)
% 1.03/1.21        | ~ (v1_relat_1 @ sk_B))),
% 1.03/1.21      inference('sup+', [status(thm)], ['52', '55'])).
% 1.03/1.21  thf('57', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.03/1.21  thf('58', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('59', plain,
% 1.03/1.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X13)
% 1.03/1.21          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 1.03/1.21          | (v2_funct_1 @ X13)
% 1.03/1.21          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.03/1.21  thf('60', plain,
% 1.03/1.21      (((v2_funct_1 @ sk_B)
% 1.03/1.21        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v1_funct_1 @ sk_B))),
% 1.03/1.21      inference('sup-', [status(thm)], ['58', '59'])).
% 1.03/1.21  thf('61', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 1.03/1.21      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.03/1.21  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 1.03/1.21      inference('demod', [status(thm)], ['46', '47'])).
% 1.03/1.21  thf('66', plain,
% 1.03/1.21      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['56', '57', '63', '64', '65'])).
% 1.03/1.21  thf('67', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         (m1_subset_1 @ (k6_relat_1 @ X12) @ 
% 1.03/1.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 1.03/1.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.03/1.21  thf(redefinition_r2_relset_1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.03/1.21  thf('68', plain,
% 1.03/1.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ((X8) = (X11))
% 1.03/1.21          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.03/1.21  thf('69', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 1.03/1.21          | ((k6_relat_1 @ X0) = (X1))
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['67', '68'])).
% 1.03/1.21  thf('70', plain,
% 1.03/1.21      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 1.03/1.21        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.03/1.21             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['66', '69'])).
% 1.03/1.21  thf('71', plain,
% 1.03/1.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.03/1.21           (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.03/1.21        | ~ (v1_relat_1 @ sk_B)
% 1.03/1.21        | ~ (v1_funct_1 @ sk_B)
% 1.03/1.21        | ~ (v2_funct_1 @ sk_B)
% 1.03/1.21        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['35', '70'])).
% 1.03/1.21  thf('72', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.03/1.21  thf('73', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         (m1_subset_1 @ (k6_relat_1 @ X12) @ 
% 1.03/1.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 1.03/1.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.03/1.21  thf('74', plain,
% 1.03/1.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | (r2_relset_1 @ X9 @ X10 @ X8 @ X11)
% 1.03/1.21          | ((X8) != (X11)))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.03/1.21  thf('75', plain,
% 1.03/1.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.21         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.03/1.21      inference('simplify', [status(thm)], ['74'])).
% 1.03/1.21  thf('76', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['73', '75'])).
% 1.03/1.21  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 1.03/1.21      inference('demod', [status(thm)], ['46', '47'])).
% 1.03/1.21  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('79', plain, ((v2_funct_1 @ sk_B)),
% 1.03/1.21      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.03/1.21  thf('80', plain,
% 1.03/1.21      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['71', '72', '76', '77', '78', '79'])).
% 1.03/1.21  thf('81', plain,
% 1.03/1.21      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.03/1.21         = (k6_relat_1 @ sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['33', '34', '80'])).
% 1.03/1.21  thf('82', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 1.03/1.21  thf('83', plain,
% 1.03/1.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21           (k6_partfun1 @ sk_A)))
% 1.03/1.21         <= (~
% 1.03/1.21             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21               (k6_partfun1 @ sk_A))))),
% 1.03/1.21      inference('split', [status(esa)], ['0'])).
% 1.03/1.21  thf('84', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.21  thf('85', plain,
% 1.03/1.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21           (k6_relat_1 @ sk_A)))
% 1.03/1.21         <= (~
% 1.03/1.21             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21               (k6_partfun1 @ sk_A))))),
% 1.03/1.21      inference('demod', [status(thm)], ['83', '84'])).
% 1.03/1.21  thf('86', plain,
% 1.03/1.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21            sk_B) @ 
% 1.03/1.21           (k6_relat_1 @ sk_A)))
% 1.03/1.21         <= (~
% 1.03/1.21             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21               (k6_partfun1 @ sk_A))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['82', '85'])).
% 1.03/1.21  thf('87', plain,
% 1.03/1.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.03/1.21           (k6_relat_1 @ sk_A)))
% 1.03/1.21         <= (~
% 1.03/1.21             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21               (k6_partfun1 @ sk_A))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['81', '86'])).
% 1.03/1.21  thf('88', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['73', '75'])).
% 1.03/1.21  thf('89', plain,
% 1.03/1.21      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21         (k6_partfun1 @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['87', '88'])).
% 1.03/1.21  thf('90', plain,
% 1.03/1.21      (~
% 1.03/1.21       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.21          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.21         (k6_partfun1 @ sk_A))) | 
% 1.03/1.21       ~
% 1.03/1.21       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.03/1.21          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.03/1.21         (k6_partfun1 @ sk_A)))),
% 1.03/1.21      inference('split', [status(esa)], ['0'])).
% 1.03/1.21  thf('91', plain,
% 1.03/1.21      (~
% 1.03/1.21       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.21          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.03/1.21         (k6_partfun1 @ sk_A)))),
% 1.03/1.21      inference('sat_resolution*', [status(thm)], ['89', '90'])).
% 1.03/1.21  thf('92', plain,
% 1.03/1.21      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21          (k6_relat_1 @ sk_A))),
% 1.03/1.21      inference('simpl_trail', [status(thm)], ['11', '91'])).
% 1.03/1.21  thf('93', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('94', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('95', plain,
% 1.03/1.21      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.03/1.21          | ~ (v1_funct_1 @ X20)
% 1.03/1.21          | ~ (v1_funct_1 @ X23)
% 1.03/1.21          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.03/1.21          | ((k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23)
% 1.03/1.21              = (k5_relat_1 @ X20 @ X23)))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.03/1.21  thf('96', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.03/1.21            = (k5_relat_1 @ sk_B @ X0))
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ sk_B))),
% 1.03/1.21      inference('sup-', [status(thm)], ['94', '95'])).
% 1.03/1.21  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('98', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.03/1.21            = (k5_relat_1 @ sk_B @ X0))
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.21          | ~ (v1_funct_1 @ X0))),
% 1.03/1.21      inference('demod', [status(thm)], ['96', '97'])).
% 1.03/1.21  thf('99', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.21            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['93', '98'])).
% 1.03/1.21  thf('100', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('101', plain,
% 1.03/1.21      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 1.03/1.21         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('demod', [status(thm)], ['99', '100'])).
% 1.03/1.21  thf('102', plain,
% 1.03/1.21      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['92', '101'])).
% 1.03/1.21  thf('103', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         (m1_subset_1 @ (k6_relat_1 @ X12) @ 
% 1.03/1.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 1.03/1.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.03/1.21  thf('104', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('105', plain,
% 1.03/1.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X13)
% 1.03/1.21          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 1.03/1.21          | (v2_funct_2 @ X13 @ X15)
% 1.03/1.21          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.03/1.21  thf('106', plain,
% 1.03/1.21      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.03/1.21        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['104', '105'])).
% 1.03/1.21  thf('107', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('108', plain,
% 1.03/1.21      (![X18 : $i, X19 : $i]:
% 1.03/1.21         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 1.03/1.21          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.21          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.21          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.21          | ~ (v1_funct_1 @ X19))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.03/1.21  thf('109', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ sk_B)
% 1.03/1.21        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 1.03/1.21      inference('sup-', [status(thm)], ['107', '108'])).
% 1.03/1.21  thf('110', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('111', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('112', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('113', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 1.03/1.21  thf('114', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.03/1.21  thf('115', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('116', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['106', '114', '115'])).
% 1.03/1.21  thf('117', plain,
% 1.03/1.21      (![X16 : $i, X17 : $i]:
% 1.03/1.21         (~ (v2_funct_2 @ X17 @ X16)
% 1.03/1.21          | ((k2_relat_1 @ X17) = (X16))
% 1.03/1.21          | ~ (v5_relat_1 @ X17 @ X16)
% 1.03/1.21          | ~ (v1_relat_1 @ X17))),
% 1.03/1.21      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.03/1.21  thf('118', plain,
% 1.03/1.21      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.03/1.21        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['116', '117'])).
% 1.03/1.21  thf('119', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('120', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.03/1.21          | (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (v1_relat_1 @ X1))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.03/1.21  thf('121', plain,
% 1.03/1.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.03/1.21        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['119', '120'])).
% 1.03/1.21  thf('122', plain,
% 1.03/1.21      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.03/1.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.03/1.21  thf('123', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['121', '122'])).
% 1.03/1.21  thf('124', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('125', plain,
% 1.03/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.21         ((v5_relat_1 @ X5 @ X7)
% 1.03/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.21  thf('126', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.03/1.21      inference('sup-', [status(thm)], ['124', '125'])).
% 1.03/1.21  thf('127', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['118', '123', '126'])).
% 1.03/1.21  thf('128', plain,
% 1.03/1.21      (![X4 : $i]:
% 1.03/1.21         (~ (v2_funct_1 @ X4)
% 1.03/1.21          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.03/1.21              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.03/1.21          | ~ (v1_funct_1 @ X4)
% 1.03/1.21          | ~ (v1_relat_1 @ X4))),
% 1.03/1.21      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.03/1.21  thf('129', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v2_funct_1 @ X0))),
% 1.03/1.21      inference('sup+', [status(thm)], ['53', '54'])).
% 1.03/1.21  thf('130', plain,
% 1.03/1.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ((X8) = (X11))
% 1.03/1.21          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.03/1.21  thf('131', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (v2_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.21               (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ X1)
% 1.03/1.21          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) = (X1))
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ 
% 1.03/1.21               (k1_zfmisc_1 @ 
% 1.03/1.21                (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['129', '130'])).
% 1.03/1.21  thf('132', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.21             (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v2_funct_1 @ X0)
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ 
% 1.03/1.21               (k1_zfmisc_1 @ 
% 1.03/1.21                (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.03/1.21          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) = (X1))
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v2_funct_1 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['128', '131'])).
% 1.03/1.21  thf('133', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) = (X1))
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ 
% 1.03/1.21               (k1_zfmisc_1 @ 
% 1.03/1.21                (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.03/1.21          | ~ (v2_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ~ (r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.03/1.21               (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))),
% 1.03/1.21      inference('simplify', [status(thm)], ['132'])).
% 1.03/1.21  thf('134', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X0 @ 
% 1.03/1.21             (k1_zfmisc_1 @ 
% 1.03/1.21              (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))
% 1.03/1.21          | ~ (r2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21               (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21               (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))) @ X0)
% 1.03/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21              (k2_funct_1 @ sk_B)) = (X0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['127', '133'])).
% 1.03/1.21  thf('135', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['118', '123', '126'])).
% 1.03/1.21  thf('136', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['118', '123', '126'])).
% 1.03/1.21  thf('137', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['118', '123', '126'])).
% 1.03/1.21  thf('138', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['118', '123', '126'])).
% 1.03/1.21  thf('139', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['121', '122'])).
% 1.03/1.21  thf('140', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('141', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('142', plain,
% 1.03/1.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X13)
% 1.03/1.21          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 1.03/1.21          | (v2_funct_1 @ X13)
% 1.03/1.21          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.03/1.21  thf('143', plain,
% 1.03/1.21      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['141', '142'])).
% 1.03/1.21  thf('144', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.03/1.21  thf('145', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('146', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['143', '144', '145'])).
% 1.03/1.21  thf('147', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.03/1.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ X0)
% 1.03/1.21          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21              (k2_funct_1 @ sk_B)) = (X0)))),
% 1.03/1.21      inference('demod', [status(thm)],
% 1.03/1.21                ['134', '135', '136', '137', '138', '139', '140', '146'])).
% 1.03/1.21  thf('148', plain,
% 1.03/1.21      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.03/1.21          = (k6_relat_1 @ sk_A))
% 1.03/1.21        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.03/1.21             (k6_relat_1 @ sk_A)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['103', '147'])).
% 1.03/1.21  thf('149', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['73', '75'])).
% 1.03/1.21  thf('150', plain,
% 1.03/1.21      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.03/1.21         = (k6_relat_1 @ sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['148', '149'])).
% 1.03/1.21  thf('151', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('152', plain,
% 1.03/1.21      (![X18 : $i, X19 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.21          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.21          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.21          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.21          | ~ (v1_funct_1 @ X19))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.03/1.21  thf('153', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['151', '152'])).
% 1.03/1.21  thf('154', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('155', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('156', plain,
% 1.03/1.21      (![X18 : $i, X19 : $i]:
% 1.03/1.21         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 1.03/1.21          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 1.03/1.21          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.21          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 1.03/1.21          | ~ (v1_funct_1 @ X19))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.03/1.21  thf('157', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ sk_B)
% 1.03/1.21        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 1.03/1.21      inference('sup-', [status(thm)], ['155', '156'])).
% 1.03/1.21  thf('158', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('159', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('160', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('161', plain, ((v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 1.03/1.21  thf('162', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 1.03/1.21  thf('163', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['161', '162'])).
% 1.03/1.21  thf('164', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.03/1.21  thf('165', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['153', '154', '163', '164'])).
% 1.03/1.21  thf('166', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('167', plain,
% 1.03/1.21      (![X26 : $i, X27 : $i]:
% 1.03/1.21         (((k2_funct_2 @ X27 @ X26) = (k2_funct_1 @ X26))
% 1.03/1.21          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 1.03/1.21          | ~ (v3_funct_2 @ X26 @ X27 @ X27)
% 1.03/1.21          | ~ (v1_funct_2 @ X26 @ X27 @ X27)
% 1.03/1.21          | ~ (v1_funct_1 @ X26))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.03/1.21  thf('168', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.03/1.21        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.03/1.21            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['166', '167'])).
% 1.03/1.21  thf('169', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('170', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['161', '162'])).
% 1.03/1.21  thf('171', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.03/1.21  thf('172', plain,
% 1.03/1.21      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.03/1.21         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 1.03/1.21  thf('173', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['165', '172'])).
% 1.03/1.21  thf('174', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('175', plain,
% 1.03/1.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.03/1.21          | ((X8) = (X11))
% 1.03/1.21          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.03/1.21  thf('176', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0)
% 1.03/1.21          | ((sk_B) = (X0))
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['174', '175'])).
% 1.03/1.21  thf('177', plain,
% 1.03/1.21      ((((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.03/1.21        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.21             (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['173', '176'])).
% 1.03/1.21  thf('178', plain,
% 1.03/1.21      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.03/1.21         = (k6_relat_1 @ sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['33', '34', '80'])).
% 1.03/1.21  thf('179', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(t87_funct_2, axiom,
% 1.03/1.21    (![A:$i,B:$i]:
% 1.03/1.21     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.03/1.21         ( v3_funct_2 @ B @ A @ A ) & 
% 1.03/1.21         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.03/1.21       ( ![C:$i]:
% 1.03/1.21         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.03/1.21             ( v3_funct_2 @ C @ A @ A ) & 
% 1.03/1.21             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.03/1.21           ( ( r2_relset_1 @
% 1.03/1.21               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.03/1.21               ( k6_partfun1 @ A ) ) =>
% 1.03/1.21             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 1.03/1.21  thf('180', plain,
% 1.03/1.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X29)
% 1.03/1.21          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 1.03/1.21          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 1.03/1.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.03/1.21          | (r2_relset_1 @ X30 @ X30 @ X29 @ (k2_funct_2 @ X30 @ X31))
% 1.03/1.21          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 1.03/1.21               (k1_partfun1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X29) @ 
% 1.03/1.21               (k6_partfun1 @ X30))
% 1.03/1.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.03/1.21          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 1.03/1.21          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 1.03/1.21          | ~ (v1_funct_1 @ X31))),
% 1.03/1.21      inference('cnf', [status(esa)], [t87_funct_2])).
% 1.03/1.21  thf('181', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.21  thf('182', plain,
% 1.03/1.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X29)
% 1.03/1.21          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 1.03/1.21          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 1.03/1.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.03/1.21          | (r2_relset_1 @ X30 @ X30 @ X29 @ (k2_funct_2 @ X30 @ X31))
% 1.03/1.21          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 1.03/1.21               (k1_partfun1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X29) @ 
% 1.03/1.21               (k6_relat_1 @ X30))
% 1.03/1.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 1.03/1.21          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 1.03/1.21          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 1.03/1.21          | ~ (v1_funct_1 @ X31))),
% 1.03/1.21      inference('demod', [status(thm)], ['180', '181'])).
% 1.03/1.21  thf('183', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.03/1.21          | ~ (v3_funct_2 @ X0 @ sk_A @ sk_A)
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.03/1.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B) @ 
% 1.03/1.21               (k6_relat_1 @ sk_A))
% 1.03/1.21          | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_2 @ sk_A @ X0))
% 1.03/1.21          | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.03/1.21          | ~ (v1_funct_1 @ sk_B))),
% 1.03/1.21      inference('sup-', [status(thm)], ['179', '182'])).
% 1.03/1.21  thf('184', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('185', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('186', plain, ((v1_funct_1 @ sk_B)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('187', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.03/1.21          | ~ (v3_funct_2 @ X0 @ sk_A @ sk_A)
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.03/1.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.03/1.21               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B) @ 
% 1.03/1.21               (k6_relat_1 @ sk_A))
% 1.03/1.21          | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_2 @ sk_A @ X0)))),
% 1.03/1.21      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 1.03/1.21  thf('188', plain,
% 1.03/1.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.03/1.21           (k6_relat_1 @ sk_A))
% 1.03/1.21        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 1.03/1.21           (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))
% 1.03/1.21        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.03/1.21        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.03/1.21        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['178', '187'])).
% 1.03/1.21  thf('189', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['73', '75'])).
% 1.03/1.21  thf('190', plain,
% 1.03/1.21      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.03/1.21         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 1.03/1.21  thf('191', plain,
% 1.03/1.21      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.03/1.21      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.03/1.21  thf('192', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.03/1.21  thf('193', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.03/1.21      inference('demod', [status(thm)], ['161', '162'])).
% 1.03/1.21  thf('194', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.03/1.21      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.21  thf('195', plain,
% 1.03/1.21      ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('demod', [status(thm)],
% 1.03/1.21                ['188', '189', '190', '191', '192', '193', '194'])).
% 1.03/1.21  thf('196', plain, (((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.03/1.21      inference('demod', [status(thm)], ['177', '195'])).
% 1.03/1.21  thf('197', plain,
% 1.03/1.21      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['150', '196'])).
% 1.03/1.21  thf('198', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['73', '75'])).
% 1.03/1.21  thf('199', plain, ($false),
% 1.03/1.21      inference('demod', [status(thm)], ['102', '197', '198'])).
% 1.03/1.21  
% 1.03/1.21  % SZS output end Refutation
% 1.03/1.21  
% 1.03/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
