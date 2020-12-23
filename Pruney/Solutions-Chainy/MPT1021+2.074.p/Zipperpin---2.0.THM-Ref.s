%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8e2SXFd4H

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:23 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  334 (10200 expanded)
%              Number of leaves         :   37 (3112 expanded)
%              Depth                    :   22
%              Number of atoms          : 3594 (264724 expanded)
%              Number of equality atoms :   88 (1445 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_2 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_2 @ X16 @ X15 )
      | ( ( k2_relat_1 @ X16 )
        = X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('54',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('62',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('68',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','65','66','67'])).

thf('69',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('74',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','65','66','67'])).

thf('75',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 )
      | ( X8 != X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('76',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('80',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','84'])).

thf('86',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('88',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('93',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('107',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','107'])).

thf('109',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('111',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('113',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('116',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('127',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('130',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('136',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118','127','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('139',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('142',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('143',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('144',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('146',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('149',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('152',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('153',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('156',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['147','156'])).

thf('158',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','157'])).

thf('159',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('160',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('161',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('162',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_2 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('163',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('165',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('166',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_2 @ X16 @ X15 )
      | ( ( k2_relat_1 @ X16 )
        = X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('173',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('175',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('176',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['168','173','176'])).

thf('178',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('180',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
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
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) )
      | ~ ( r2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['168','173','176'])).

thf('186',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['168','173','176'])).

thf('187',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['168','173','176'])).

thf('188',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['168','173','176'])).

thf('189',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('190',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('191',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('192',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('193',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('195',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('196',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['184','185','186','187','188','189','190','196'])).

thf('198',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('200',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159','200'])).

thf('202',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

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

thf('203',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ( r2_relset_1 @ X31 @ X31 @ X30 @ ( k2_funct_2 @ X31 @ X32 ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X31 @ X31 @ X31 @ X32 @ X30 ) @ ( k6_partfun1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t87_funct_2])).

thf('204',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('205',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ( r2_relset_1 @ X31 @ X31 @ X30 @ ( k2_funct_2 @ X31 @ X32 ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X31 @ X31 @ X31 @ X32 @ X30 ) @ ( k6_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v3_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_2 @ sk_A @ X0 ) )
      | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['202','205'])).

thf('207',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('208',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('209',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v3_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['201','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('214',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_funct_2 @ X28 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('215',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('217',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('218',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('219',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('221',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('222',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('223',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('225',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('227',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('228',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('230',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('231',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('232',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('233',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('234',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['215','216','225','234'])).

thf('236',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('237',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['232','233'])).

thf('238',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['223','224'])).

thf('239',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('240',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['211','212','235','236','237','238','239'])).

thf('241',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('242',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ X0 )
      | ( ( k2_funct_1 @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_funct_1 @ sk_B )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['240','243'])).

thf('245',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('246',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('247',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('249',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['223','224'])).

thf('250',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['232','233'])).

thf('251',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['215','216','225','234'])).

thf('253',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['244','253'])).

thf('255',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('256',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('258',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('260',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('262',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('264',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('265',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('266',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['232','233'])).

thf('268',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('269',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['256','257','262','263','269'])).

thf('271',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','144'])).

thf('272',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( X8 = X11 )
      | ~ ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( sk_B
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['271','274'])).

thf('276',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','84'])).

thf('277',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ( r2_relset_1 @ X31 @ X31 @ X30 @ ( k2_funct_2 @ X31 @ X32 ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X31 @ X31 @ X31 @ X32 @ X30 ) @ ( k6_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('279',plain,(
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
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v3_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['279','280','281','282'])).

thf('284',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['276','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('286',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('287',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('288',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('289',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('290',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('291',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['284','285','286','287','288','289','290'])).

thf('292',plain,
    ( sk_B
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['275','291'])).

thf('293',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['270','292'])).

thf('294',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('295',plain,(
    $false ),
    inference(demod,[status(thm)],['113','293','294'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8e2SXFd4H
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.07/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.26  % Solved by: fo/fo7.sh
% 1.07/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.26  % done 789 iterations in 0.812s
% 1.07/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.26  % SZS output start Refutation
% 1.07/1.26  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.07/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.26  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.07/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.26  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.07/1.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.26  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.26  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.07/1.26  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.26  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.07/1.26  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.07/1.26  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.07/1.26  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.07/1.26  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.26  thf(t61_funct_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.26       ( ( v2_funct_1 @ A ) =>
% 1.07/1.26         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.07/1.26             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.07/1.26           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.07/1.26             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.07/1.26  thf('0', plain,
% 1.07/1.26      (![X4 : $i]:
% 1.07/1.26         (~ (v2_funct_1 @ X4)
% 1.07/1.26          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.07/1.26              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 1.07/1.26          | ~ (v1_funct_1 @ X4)
% 1.07/1.26          | ~ (v1_relat_1 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.26  thf(t88_funct_2, conjecture,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.07/1.26       ( ( r2_relset_1 @
% 1.07/1.26           A @ A @ 
% 1.07/1.26           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.07/1.26           ( k6_partfun1 @ A ) ) & 
% 1.07/1.26         ( r2_relset_1 @
% 1.07/1.26           A @ A @ 
% 1.07/1.26           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.07/1.26           ( k6_partfun1 @ A ) ) ) ))).
% 1.07/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.26    (~( ![A:$i,B:$i]:
% 1.07/1.26        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.07/1.26            ( v3_funct_2 @ B @ A @ A ) & 
% 1.07/1.26            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.07/1.26          ( ( r2_relset_1 @
% 1.07/1.26              A @ A @ 
% 1.07/1.26              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.07/1.26              ( k6_partfun1 @ A ) ) & 
% 1.07/1.26            ( r2_relset_1 @
% 1.07/1.26              A @ A @ 
% 1.07/1.26              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.07/1.26              ( k6_partfun1 @ A ) ) ) ) )),
% 1.07/1.26    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.07/1.26  thf('1', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26           (k6_partfun1 @ sk_A))
% 1.07/1.26        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26             (k6_partfun1 @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('2', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26           (k6_partfun1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('split', [status(esa)], ['1'])).
% 1.07/1.26  thf(redefinition_k6_partfun1, axiom,
% 1.07/1.26    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.07/1.26  thf('3', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.26  thf('4', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.26  thf('5', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(redefinition_k2_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.07/1.26       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.07/1.26  thf('6', plain,
% 1.07/1.26      (![X27 : $i, X28 : $i]:
% 1.07/1.26         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 1.07/1.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 1.07/1.26          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 1.07/1.26          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 1.07/1.26          | ~ (v1_funct_1 @ X27))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.07/1.26  thf('7', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['5', '6'])).
% 1.07/1.26  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.07/1.26  thf('12', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26            (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('demod', [status(thm)], ['4', '11'])).
% 1.07/1.26  thf('13', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('14', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(dt_k2_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.07/1.26       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.07/1.26         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.07/1.26         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.07/1.26         ( m1_subset_1 @
% 1.07/1.26           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.07/1.26  thf('15', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('16', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['14', '15'])).
% 1.07/1.26  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.07/1.26  thf('21', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf(redefinition_k1_partfun1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.26         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( v1_funct_1 @ F ) & 
% 1.07/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.26       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.07/1.26  thf('22', plain,
% 1.07/1.26      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.07/1.26          | ~ (v1_funct_1 @ X21)
% 1.07/1.26          | ~ (v1_funct_1 @ X24)
% 1.07/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.07/1.26          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 1.07/1.26              = (k5_relat_1 @ X21 @ X24)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.07/1.26  thf('23', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.07/1.26            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.26  thf('24', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('25', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((v1_funct_1 @ (k2_funct_2 @ X17 @ X18))
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('26', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['24', '25'])).
% 1.07/1.26  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 1.07/1.26  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.07/1.26  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('33', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.07/1.26            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '32'])).
% 1.07/1.26  thf('34', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['13', '33'])).
% 1.07/1.26  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('36', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.07/1.26         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.07/1.26  thf('37', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | (v2_funct_2 @ X12 @ X14)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.07/1.26  thf('38', plain,
% 1.07/1.26      (((v2_funct_2 @ sk_B @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['36', '37'])).
% 1.07/1.26  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.07/1.26  thf(d3_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.07/1.26       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.07/1.26  thf('42', plain,
% 1.07/1.26      (![X15 : $i, X16 : $i]:
% 1.07/1.26         (~ (v2_funct_2 @ X16 @ X15)
% 1.07/1.26          | ((k2_relat_1 @ X16) = (X15))
% 1.07/1.26          | ~ (v5_relat_1 @ X16 @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.07/1.26  thf('43', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ sk_B)
% 1.07/1.26        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.07/1.26        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['41', '42'])).
% 1.07/1.26  thf('44', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.26  thf('45', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.26          | (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('46', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf(fc6_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.26  thf('47', plain,
% 1.07/1.26      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['46', '47'])).
% 1.07/1.26  thf('49', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.26  thf('50', plain,
% 1.07/1.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.26         ((v5_relat_1 @ X5 @ X7)
% 1.07/1.26          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.26  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.07/1.26      inference('sup-', [status(thm)], ['49', '50'])).
% 1.07/1.26  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.07/1.26  thf('53', plain,
% 1.07/1.26      (![X4 : $i]:
% 1.07/1.26         (~ (v2_funct_1 @ X4)
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.07/1.26              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.07/1.26          | ~ (v1_funct_1 @ X4)
% 1.07/1.26          | ~ (v1_relat_1 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.26  thf(dt_k6_partfun1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( m1_subset_1 @
% 1.07/1.26         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.07/1.26       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.07/1.26  thf('54', plain,
% 1.07/1.26      (![X20 : $i]:
% 1.07/1.26         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 1.07/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.07/1.26  thf('55', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.26  thf('56', plain,
% 1.07/1.26      (![X20 : $i]:
% 1.07/1.26         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 1.07/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.07/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.07/1.26  thf('57', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v2_funct_1 @ X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['53', '56'])).
% 1.07/1.26  thf('58', plain,
% 1.07/1.26      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.07/1.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 1.07/1.26        | ~ (v2_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.07/1.26      inference('sup+', [status(thm)], ['52', '57'])).
% 1.07/1.26  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.07/1.26  thf('60', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('61', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | (v2_funct_1 @ X12)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.07/1.26  thf('62', plain,
% 1.07/1.26      (((v2_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.26  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.07/1.26  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['46', '47'])).
% 1.07/1.26  thf('68', plain,
% 1.07/1.26      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 1.07/1.26  thf('69', plain,
% 1.07/1.26      (![X20 : $i]:
% 1.07/1.26         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 1.07/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.07/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.07/1.26  thf(redefinition_r2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.26     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.07/1.26  thf('70', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ((X8) = (X11))
% 1.07/1.26          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.26  thf('71', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 1.07/1.26          | ((k6_relat_1 @ X0) = (X1))
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['69', '70'])).
% 1.07/1.26  thf('72', plain,
% 1.07/1.26      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 1.07/1.26        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.26             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['68', '71'])).
% 1.07/1.26  thf('73', plain,
% 1.07/1.26      (![X4 : $i]:
% 1.07/1.26         (~ (v2_funct_1 @ X4)
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.07/1.26              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.07/1.26          | ~ (v1_funct_1 @ X4)
% 1.07/1.26          | ~ (v1_relat_1 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.26  thf('74', plain,
% 1.07/1.26      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 1.07/1.26  thf('75', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | (r2_relset_1 @ X9 @ X10 @ X8 @ X11)
% 1.07/1.26          | ((X8) != (X11)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.26  thf('76', plain,
% 1.07/1.26      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.07/1.26      inference('simplify', [status(thm)], ['75'])).
% 1.07/1.26  thf('77', plain,
% 1.07/1.26      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 1.07/1.26        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['74', '76'])).
% 1.07/1.26  thf('78', plain,
% 1.07/1.26      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.07/1.26         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 1.07/1.26        | ~ (v1_relat_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v2_funct_1 @ sk_B))),
% 1.07/1.26      inference('sup+', [status(thm)], ['73', '77'])).
% 1.07/1.26  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.07/1.26  thf('80', plain, ((v1_relat_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['46', '47'])).
% 1.07/1.26  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('82', plain, ((v2_funct_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.07/1.26  thf('83', plain,
% 1.07/1.26      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.26        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 1.07/1.26  thf('84', plain,
% 1.07/1.26      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['72', '83'])).
% 1.07/1.26  thf('85', plain,
% 1.07/1.26      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.07/1.26         = (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['34', '35', '84'])).
% 1.07/1.26  thf('86', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.07/1.26  thf('87', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26           (k6_partfun1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('split', [status(esa)], ['1'])).
% 1.07/1.26  thf('88', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.26  thf('89', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('demod', [status(thm)], ['87', '88'])).
% 1.07/1.26  thf('90', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26            sk_B) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['86', '89'])).
% 1.07/1.26  thf('91', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26               (k6_partfun1 @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['85', '90'])).
% 1.07/1.26  thf('92', plain,
% 1.07/1.26      (![X20 : $i]:
% 1.07/1.26         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 1.07/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.07/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.07/1.26  thf('93', plain,
% 1.07/1.26      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.07/1.26      inference('simplify', [status(thm)], ['75'])).
% 1.07/1.26  thf('94', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.26  thf('95', plain,
% 1.07/1.26      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26         (k6_partfun1 @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['91', '94'])).
% 1.07/1.26  thf('96', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26         (k6_partfun1 @ sk_A))) | 
% 1.07/1.26       ~
% 1.07/1.26       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.07/1.26         (k6_partfun1 @ sk_A)))),
% 1.07/1.26      inference('split', [status(esa)], ['1'])).
% 1.07/1.26  thf('97', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.07/1.26         (k6_partfun1 @ sk_A)))),
% 1.07/1.26      inference('sat_resolution*', [status(thm)], ['95', '96'])).
% 1.07/1.26  thf('98', plain,
% 1.07/1.26      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26          (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('simpl_trail', [status(thm)], ['12', '97'])).
% 1.07/1.26  thf('99', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('100', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('101', plain,
% 1.07/1.26      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.07/1.26          | ~ (v1_funct_1 @ X21)
% 1.07/1.26          | ~ (v1_funct_1 @ X24)
% 1.07/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.07/1.26          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 1.07/1.26              = (k5_relat_1 @ X21 @ X24)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.07/1.26  thf('102', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.07/1.26            = (k5_relat_1 @ sk_B @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['100', '101'])).
% 1.07/1.26  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('104', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.07/1.26            = (k5_relat_1 @ sk_B @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['102', '103'])).
% 1.07/1.26  thf('105', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['99', '104'])).
% 1.07/1.26  thf('106', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('107', plain,
% 1.07/1.26      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['105', '106'])).
% 1.07/1.26  thf('108', plain,
% 1.07/1.26      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['98', '107'])).
% 1.07/1.26  thf('109', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A))
% 1.07/1.26        | ~ (v1_relat_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v2_funct_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['0', '108'])).
% 1.07/1.26  thf('110', plain, ((v1_relat_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['46', '47'])).
% 1.07/1.26  thf('111', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('112', plain, ((v2_funct_1 @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.07/1.26  thf('113', plain,
% 1.07/1.26      (~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 1.07/1.26          (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 1.07/1.26  thf('114', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('115', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('116', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('117', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['115', '116'])).
% 1.07/1.26  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('119', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('120', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((v1_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('121', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['119', '120'])).
% 1.07/1.26  thf('122', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('123', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('124', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('125', plain, ((v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 1.07/1.26  thf('126', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.07/1.26  thf('127', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('128', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('129', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((v3_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('130', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['128', '129'])).
% 1.07/1.26  thf('131', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('132', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('133', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('134', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 1.07/1.26  thf('135', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.07/1.26  thf('136', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('137', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['117', '118', '127', '136'])).
% 1.07/1.26  thf('138', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('139', plain,
% 1.07/1.26      (![X27 : $i, X28 : $i]:
% 1.07/1.26         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 1.07/1.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 1.07/1.26          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 1.07/1.26          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 1.07/1.26          | ~ (v1_funct_1 @ X27))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.07/1.26  thf('140', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.07/1.26            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['138', '139'])).
% 1.07/1.26  thf('141', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('142', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('143', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('144', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.07/1.26  thf('145', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('146', plain,
% 1.07/1.26      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.07/1.26          | ~ (v1_funct_1 @ X21)
% 1.07/1.26          | ~ (v1_funct_1 @ X24)
% 1.07/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.07/1.26          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 1.07/1.26              = (k5_relat_1 @ X21 @ X24)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.07/1.26  thf('147', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 1.07/1.26            (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ X0)
% 1.07/1.26            = (k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['145', '146'])).
% 1.07/1.26  thf('148', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('149', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((v1_funct_1 @ (k2_funct_2 @ X17 @ X18))
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('150', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['148', '149'])).
% 1.07/1.26  thf('151', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('152', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('153', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('154', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 1.07/1.26  thf('155', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.07/1.26  thf('156', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['154', '155'])).
% 1.07/1.26  thf('157', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 1.07/1.26            (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ X0)
% 1.07/1.26            = (k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['147', '156'])).
% 1.07/1.26  thf('158', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26            (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.07/1.26            = (k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26               (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['114', '157'])).
% 1.07/1.26  thf('159', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('160', plain,
% 1.07/1.26      (![X20 : $i]:
% 1.07/1.26         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 1.07/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.07/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.07/1.26  thf('161', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('162', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | (v2_funct_2 @ X12 @ X14)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.07/1.26  thf('163', plain,
% 1.07/1.26      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['161', '162'])).
% 1.07/1.26  thf('164', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('165', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('166', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['163', '164', '165'])).
% 1.07/1.26  thf('167', plain,
% 1.07/1.26      (![X15 : $i, X16 : $i]:
% 1.07/1.26         (~ (v2_funct_2 @ X16 @ X15)
% 1.07/1.26          | ((k2_relat_1 @ X16) = (X15))
% 1.07/1.26          | ~ (v5_relat_1 @ X16 @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.07/1.26  thf('168', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.07/1.26        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['166', '167'])).
% 1.07/1.26  thf('169', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('170', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.26          | (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('171', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.07/1.26        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['169', '170'])).
% 1.07/1.26  thf('172', plain,
% 1.07/1.26      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('173', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['171', '172'])).
% 1.07/1.26  thf('174', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('175', plain,
% 1.07/1.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.26         ((v5_relat_1 @ X5 @ X7)
% 1.07/1.26          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.26  thf('176', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.07/1.26      inference('sup-', [status(thm)], ['174', '175'])).
% 1.07/1.26  thf('177', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['168', '173', '176'])).
% 1.07/1.26  thf('178', plain,
% 1.07/1.26      (![X4 : $i]:
% 1.07/1.26         (~ (v2_funct_1 @ X4)
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.07/1.26              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.07/1.26          | ~ (v1_funct_1 @ X4)
% 1.07/1.26          | ~ (v1_relat_1 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.26  thf('179', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v2_funct_1 @ X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['53', '56'])).
% 1.07/1.26  thf('180', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ((X8) = (X11))
% 1.07/1.26          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.26  thf('181', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v2_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.07/1.26               (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ X1)
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) = (X1))
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['179', '180'])).
% 1.07/1.26  thf('182', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.07/1.26             (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v2_funct_1 @ X0)
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) = (X1))
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v2_funct_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['178', '181'])).
% 1.07/1.26  thf('183', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) = (X1))
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.07/1.26          | ~ (v2_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.07/1.26               (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))),
% 1.07/1.26      inference('simplify', [status(thm)], ['182'])).
% 1.07/1.26  thf('184', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ 
% 1.07/1.26             (k1_zfmisc_1 @ 
% 1.07/1.26              (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))
% 1.07/1.26          | ~ (r2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26               (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26               (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))) @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26              (k2_funct_1 @ sk_B)) = (X0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['177', '183'])).
% 1.07/1.26  thf('185', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['168', '173', '176'])).
% 1.07/1.26  thf('186', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['168', '173', '176'])).
% 1.07/1.26  thf('187', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['168', '173', '176'])).
% 1.07/1.26  thf('188', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['168', '173', '176'])).
% 1.07/1.26  thf('189', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['171', '172'])).
% 1.07/1.26  thf('190', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('191', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('192', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | (v2_funct_1 @ X12)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.07/1.26  thf('193', plain,
% 1.07/1.26      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['191', '192'])).
% 1.07/1.26  thf('194', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('195', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('196', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.07/1.26  thf('197', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ X0)
% 1.07/1.26          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26              (k2_funct_1 @ sk_B)) = (X0)))),
% 1.07/1.26      inference('demod', [status(thm)],
% 1.07/1.26                ['184', '185', '186', '187', '188', '189', '190', '196'])).
% 1.07/1.26  thf('198', plain,
% 1.07/1.26      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.07/1.26          = (k6_relat_1 @ sk_A))
% 1.07/1.26        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.26             (k6_relat_1 @ sk_A)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['160', '197'])).
% 1.07/1.26  thf('199', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.26  thf('200', plain,
% 1.07/1.26      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['198', '199'])).
% 1.07/1.26  thf('201', plain,
% 1.07/1.26      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.07/1.26         (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['158', '159', '200'])).
% 1.07/1.26  thf('202', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf(t87_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.07/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.07/1.26       ( ![C:$i]:
% 1.07/1.26         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.07/1.26             ( v3_funct_2 @ C @ A @ A ) & 
% 1.07/1.26             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.07/1.26           ( ( r2_relset_1 @
% 1.07/1.26               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.07/1.26               ( k6_partfun1 @ A ) ) =>
% 1.07/1.26             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 1.07/1.26  thf('203', plain,
% 1.07/1.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X30)
% 1.07/1.26          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 1.07/1.26          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 1.07/1.26          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.07/1.26          | (r2_relset_1 @ X31 @ X31 @ X30 @ (k2_funct_2 @ X31 @ X32))
% 1.07/1.26          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 1.07/1.26               (k1_partfun1 @ X31 @ X31 @ X31 @ X31 @ X32 @ X30) @ 
% 1.07/1.26               (k6_partfun1 @ X31))
% 1.07/1.26          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.07/1.26          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 1.07/1.26          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 1.07/1.26          | ~ (v1_funct_1 @ X32))),
% 1.07/1.26      inference('cnf', [status(esa)], [t87_funct_2])).
% 1.07/1.26  thf('204', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.26  thf('205', plain,
% 1.07/1.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X30)
% 1.07/1.26          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 1.07/1.26          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 1.07/1.26          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.07/1.26          | (r2_relset_1 @ X31 @ X31 @ X30 @ (k2_funct_2 @ X31 @ X32))
% 1.07/1.26          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 1.07/1.26               (k1_partfun1 @ X31 @ X31 @ X31 @ X31 @ X32 @ X30) @ 
% 1.07/1.26               (k6_relat_1 @ X31))
% 1.07/1.26          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.07/1.26          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 1.07/1.26          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 1.07/1.26          | ~ (v1_funct_1 @ X32))),
% 1.07/1.26      inference('demod', [status(thm)], ['203', '204'])).
% 1.07/1.26  thf('206', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v3_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ 
% 1.07/1.26                (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26               (k6_relat_1 @ sk_A))
% 1.07/1.26          | (r2_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26             (k2_funct_2 @ sk_A @ X0))
% 1.07/1.26          | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['202', '205'])).
% 1.07/1.26  thf('207', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('208', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('209', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('210', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v3_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ 
% 1.07/1.26                (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26               (k6_relat_1 @ sk_A))
% 1.07/1.26          | (r2_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26             (k2_funct_2 @ sk_A @ X0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 1.07/1.26  thf('211', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A))
% 1.07/1.26        | (r2_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26           (k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))
% 1.07/1.26        | ~ (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['201', '210'])).
% 1.07/1.26  thf('212', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.26  thf('213', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('214', plain,
% 1.07/1.26      (![X27 : $i, X28 : $i]:
% 1.07/1.26         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 1.07/1.26          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 1.07/1.26          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 1.07/1.26          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 1.07/1.26          | ~ (v1_funct_1 @ X27))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.07/1.26  thf('215', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['213', '214'])).
% 1.07/1.26  thf('216', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['154', '155'])).
% 1.07/1.26  thf('217', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('218', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((v1_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('219', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['217', '218'])).
% 1.07/1.26  thf('220', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('221', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('222', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('223', plain,
% 1.07/1.26      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 1.07/1.26  thf('224', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.07/1.26  thf('225', plain,
% 1.07/1.26      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['223', '224'])).
% 1.07/1.26  thf('226', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('227', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((v3_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('228', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['226', '227'])).
% 1.07/1.26  thf('229', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('230', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('231', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('232', plain,
% 1.07/1.26      ((v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 1.07/1.26  thf('233', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.07/1.26  thf('234', plain,
% 1.07/1.26      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['232', '233'])).
% 1.07/1.26  thf('235', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['215', '216', '225', '234'])).
% 1.07/1.26  thf('236', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('237', plain,
% 1.07/1.26      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['232', '233'])).
% 1.07/1.26  thf('238', plain,
% 1.07/1.26      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['223', '224'])).
% 1.07/1.26  thf('239', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['154', '155'])).
% 1.07/1.26  thf('240', plain,
% 1.07/1.26      ((r2_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)],
% 1.07/1.26                ['211', '212', '235', '236', '237', '238', '239'])).
% 1.07/1.26  thf('241', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('242', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ((X8) = (X11))
% 1.07/1.26          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.26  thf('243', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ X0)
% 1.07/1.26          | ((k2_funct_1 @ sk_B) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['241', '242'])).
% 1.07/1.26  thf('244', plain,
% 1.07/1.26      ((~ (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26        | ((k2_funct_1 @ sk_B)
% 1.07/1.26            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['240', '243'])).
% 1.07/1.26  thf('245', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('246', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 1.07/1.26          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 1.07/1.26          | ~ (v1_funct_1 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.07/1.26  thf('247', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | (m1_subset_1 @ 
% 1.07/1.26           (k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['245', '246'])).
% 1.07/1.26  thf('248', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['154', '155'])).
% 1.07/1.26  thf('249', plain,
% 1.07/1.26      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['223', '224'])).
% 1.07/1.26  thf('250', plain,
% 1.07/1.26      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['232', '233'])).
% 1.07/1.26  thf('251', plain,
% 1.07/1.26      ((m1_subset_1 @ 
% 1.07/1.26        (k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 1.07/1.26  thf('252', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['215', '216', '225', '234'])).
% 1.07/1.26  thf('253', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['251', '252'])).
% 1.07/1.26  thf('254', plain,
% 1.07/1.26      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['244', '253'])).
% 1.07/1.26  thf('255', plain,
% 1.07/1.26      (![X4 : $i]:
% 1.07/1.26         (~ (v2_funct_1 @ X4)
% 1.07/1.26          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.07/1.26              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 1.07/1.26          | ~ (v1_funct_1 @ X4)
% 1.07/1.26          | ~ (v1_relat_1 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.26  thf('256', plain,
% 1.07/1.26      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.07/1.26          = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))
% 1.07/1.26        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup+', [status(thm)], ['254', '255'])).
% 1.07/1.26  thf('257', plain,
% 1.07/1.26      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['198', '199'])).
% 1.07/1.26  thf('258', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('259', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.26          | (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('260', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.07/1.26        | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['258', '259'])).
% 1.07/1.26  thf('261', plain,
% 1.07/1.26      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('262', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['260', '261'])).
% 1.07/1.26  thf('263', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['154', '155'])).
% 1.07/1.26  thf('264', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('265', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | (v2_funct_1 @ X12)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.07/1.26  thf('266', plain,
% 1.07/1.26      (((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['264', '265'])).
% 1.07/1.26  thf('267', plain,
% 1.07/1.26      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['232', '233'])).
% 1.07/1.26  thf('268', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['154', '155'])).
% 1.07/1.26  thf('269', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['266', '267', '268'])).
% 1.07/1.26  thf('270', plain,
% 1.07/1.26      (((k6_relat_1 @ sk_A)
% 1.07/1.26         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 1.07/1.26      inference('demod', [status(thm)], ['256', '257', '262', '263', '269'])).
% 1.07/1.26  thf('271', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['137', '144'])).
% 1.07/1.26  thf('272', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('273', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.26          | ((X8) = (X11))
% 1.07/1.26          | ~ (r2_relset_1 @ X9 @ X10 @ X8 @ X11))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.26  thf('274', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0)
% 1.07/1.26          | ((sk_B) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['272', '273'])).
% 1.07/1.26  thf('275', plain,
% 1.07/1.26      ((((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26             (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['271', '274'])).
% 1.07/1.26  thf('276', plain,
% 1.07/1.26      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.07/1.26         = (k6_relat_1 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['34', '35', '84'])).
% 1.07/1.26  thf('277', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('278', plain,
% 1.07/1.26      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X30)
% 1.07/1.26          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 1.07/1.26          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 1.07/1.26          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.07/1.26          | (r2_relset_1 @ X31 @ X31 @ X30 @ (k2_funct_2 @ X31 @ X32))
% 1.07/1.26          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 1.07/1.26               (k1_partfun1 @ X31 @ X31 @ X31 @ X31 @ X32 @ X30) @ 
% 1.07/1.26               (k6_relat_1 @ X31))
% 1.07/1.26          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 1.07/1.26          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 1.07/1.26          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 1.07/1.26          | ~ (v1_funct_1 @ X32))),
% 1.07/1.26      inference('demod', [status(thm)], ['203', '204'])).
% 1.07/1.26  thf('279', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v3_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B) @ 
% 1.07/1.26               (k6_relat_1 @ sk_A))
% 1.07/1.26          | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_2 @ sk_A @ X0))
% 1.07/1.26          | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['277', '278'])).
% 1.07/1.26  thf('280', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('281', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('282', plain, ((v1_funct_1 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('283', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (v3_funct_2 @ X0 @ sk_A @ sk_A)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B) @ 
% 1.07/1.26               (k6_relat_1 @ sk_A))
% 1.07/1.26          | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_2 @ sk_A @ X0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['279', '280', '281', '282'])).
% 1.07/1.26  thf('284', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.26           (k6_relat_1 @ sk_A))
% 1.07/1.26        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 1.07/1.26           (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))
% 1.07/1.26        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['276', '283'])).
% 1.07/1.26  thf('285', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.26  thf('286', plain,
% 1.07/1.26      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 1.07/1.26         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.07/1.26  thf('287', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.07/1.26  thf('288', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('289', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126'])).
% 1.07/1.26  thf('290', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.26  thf('291', plain,
% 1.07/1.26      ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)],
% 1.07/1.26                ['284', '285', '286', '287', '288', '289', '290'])).
% 1.07/1.26  thf('292', plain, (((sk_B) = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['275', '291'])).
% 1.07/1.26  thf('293', plain,
% 1.07/1.26      (((k6_relat_1 @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.07/1.26      inference('demod', [status(thm)], ['270', '292'])).
% 1.07/1.26  thf('294', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.26  thf('295', plain, ($false),
% 1.07/1.26      inference('demod', [status(thm)], ['113', '293', '294'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
