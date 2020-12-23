%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rOVzwQZNdF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:16 EST 2020

% Result     : Theorem 3.37s
% Output     : Refutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 533 expanded)
%              Number of leaves         :   36 ( 177 expanded)
%              Depth                    :   17
%              Number of atoms          : 1509 (12730 expanded)
%              Number of equality atoms :   39 (  83 expanded)
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
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('33',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_2 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('47',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_2 @ X16 @ X15 )
      | ( ( k2_relat_1 @ X16 )
        = X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['52','55','58'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('60',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('61',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('70',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','59','65','66','67','73'])).

thf('75',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('76',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('86',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','87'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v3_funct_2 @ X12 @ X13 @ X14 )
      | ( v2_funct_2 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('92',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('100',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('102',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['92','100','101'])).

thf('103',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_2 @ X16 @ X15 )
      | ( ( k2_relat_1 @ X16 )
        = X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('106',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('107',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('109',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('110',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['104','107','110'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('118',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('119',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['88','116','117','118','119','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rOVzwQZNdF
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.37/3.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.37/3.58  % Solved by: fo/fo7.sh
% 3.37/3.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.37/3.58  % done 233 iterations in 3.128s
% 3.37/3.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.37/3.58  % SZS output start Refutation
% 3.37/3.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.37/3.58  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.37/3.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.37/3.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.37/3.58  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.37/3.58  thf(sk_A_type, type, sk_A: $i).
% 3.37/3.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.37/3.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.37/3.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.37/3.58  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 3.37/3.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.37/3.58  thf(sk_B_type, type, sk_B: $i).
% 3.37/3.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.37/3.58  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.37/3.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.37/3.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.37/3.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.37/3.58  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.37/3.58  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.37/3.58  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 3.37/3.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.37/3.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.37/3.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.37/3.58  thf(t61_funct_1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.58       ( ( v2_funct_1 @ A ) =>
% 3.37/3.58         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 3.37/3.58             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 3.37/3.58           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 3.37/3.58             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.37/3.58  thf('0', plain,
% 3.37/3.58      (![X1 : $i]:
% 3.37/3.58         (~ (v2_funct_1 @ X1)
% 3.37/3.58          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 3.37/3.58              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 3.37/3.58          | ~ (v1_funct_1 @ X1)
% 3.37/3.58          | ~ (v1_relat_1 @ X1))),
% 3.37/3.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 3.37/3.58  thf(t88_funct_2, conjecture,
% 3.37/3.58    (![A:$i,B:$i]:
% 3.37/3.58     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.37/3.58         ( v3_funct_2 @ B @ A @ A ) & 
% 3.37/3.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.37/3.58       ( ( r2_relset_1 @
% 3.37/3.58           A @ A @ 
% 3.37/3.58           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 3.37/3.58           ( k6_partfun1 @ A ) ) & 
% 3.37/3.58         ( r2_relset_1 @
% 3.37/3.58           A @ A @ 
% 3.37/3.58           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 3.37/3.58           ( k6_partfun1 @ A ) ) ) ))).
% 3.37/3.58  thf(zf_stmt_0, negated_conjecture,
% 3.37/3.58    (~( ![A:$i,B:$i]:
% 3.37/3.58        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.37/3.58            ( v3_funct_2 @ B @ A @ A ) & 
% 3.37/3.58            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.37/3.58          ( ( r2_relset_1 @
% 3.37/3.58              A @ A @ 
% 3.37/3.58              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 3.37/3.58              ( k6_partfun1 @ A ) ) & 
% 3.37/3.58            ( r2_relset_1 @
% 3.37/3.58              A @ A @ 
% 3.37/3.58              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 3.37/3.58              ( k6_partfun1 @ A ) ) ) ) )),
% 3.37/3.58    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 3.37/3.58  thf('1', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58           (k6_partfun1 @ sk_A))
% 3.37/3.58        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58             (k6_partfun1 @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('2', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58           (k6_partfun1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('split', [status(esa)], ['1'])).
% 3.37/3.58  thf(redefinition_k6_partfun1, axiom,
% 3.37/3.58    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.37/3.58  thf('3', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.37/3.58  thf('4', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58           (k6_relat_1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('demod', [status(thm)], ['2', '3'])).
% 3.37/3.58  thf('5', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(redefinition_k2_funct_2, axiom,
% 3.37/3.58    (![A:$i,B:$i]:
% 3.37/3.58     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.37/3.58         ( v3_funct_2 @ B @ A @ A ) & 
% 3.37/3.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.37/3.58       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 3.37/3.58  thf('6', plain,
% 3.37/3.58      (![X27 : $i, X28 : $i]:
% 3.37/3.58         (((k2_funct_2 @ X28 @ X27) = (k2_funct_1 @ X27))
% 3.37/3.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 3.37/3.58          | ~ (v3_funct_2 @ X27 @ X28 @ X28)
% 3.37/3.58          | ~ (v1_funct_2 @ X27 @ X28 @ X28)
% 3.37/3.58          | ~ (v1_funct_1 @ X27))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 3.37/3.58  thf('7', plain,
% 3.37/3.58      ((~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['5', '6'])).
% 3.37/3.58  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 3.37/3.58  thf('12', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58            (k2_funct_1 @ sk_B)) @ 
% 3.37/3.58           (k6_relat_1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('demod', [status(thm)], ['4', '11'])).
% 3.37/3.58  thf('13', plain,
% 3.37/3.58      (![X1 : $i]:
% 3.37/3.58         (~ (v2_funct_1 @ X1)
% 3.37/3.58          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 3.37/3.58              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 3.37/3.58          | ~ (v1_funct_1 @ X1)
% 3.37/3.58          | ~ (v1_relat_1 @ X1))),
% 3.37/3.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 3.37/3.58  thf('14', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('15', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(dt_k2_funct_2, axiom,
% 3.37/3.58    (![A:$i,B:$i]:
% 3.37/3.58     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.37/3.58         ( v3_funct_2 @ B @ A @ A ) & 
% 3.37/3.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.37/3.58       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 3.37/3.58         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 3.37/3.58         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 3.37/3.58         ( m1_subset_1 @
% 3.37/3.58           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 3.37/3.58  thf('16', plain,
% 3.37/3.58      (![X17 : $i, X18 : $i]:
% 3.37/3.58         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 3.37/3.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 3.37/3.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 3.37/3.58          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 3.37/3.58          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 3.37/3.58          | ~ (v1_funct_1 @ X18))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 3.37/3.58  thf('17', plain,
% 3.37/3.58      ((~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 3.37/3.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['15', '16'])).
% 3.37/3.58  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('20', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('21', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 3.37/3.58  thf('22', plain,
% 3.37/3.58      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 3.37/3.58  thf(redefinition_k1_partfun1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.37/3.58     ( ( ( v1_funct_1 @ E ) & 
% 3.37/3.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.37/3.58         ( v1_funct_1 @ F ) & 
% 3.37/3.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.37/3.58       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.37/3.58  thf('23', plain,
% 3.37/3.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.37/3.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.37/3.58          | ~ (v1_funct_1 @ X21)
% 3.37/3.58          | ~ (v1_funct_1 @ X24)
% 3.37/3.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.37/3.58          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 3.37/3.58              = (k5_relat_1 @ X21 @ X24)))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.37/3.58  thf('24', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.37/3.58         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 3.37/3.58            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.37/3.58          | ~ (v1_funct_1 @ X0)
% 3.37/3.58          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['22', '23'])).
% 3.37/3.58  thf('25', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('26', plain,
% 3.37/3.58      (![X17 : $i, X18 : $i]:
% 3.37/3.58         ((v1_funct_1 @ (k2_funct_2 @ X17 @ X18))
% 3.37/3.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 3.37/3.58          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 3.37/3.58          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 3.37/3.58          | ~ (v1_funct_1 @ X18))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 3.37/3.58  thf('27', plain,
% 3.37/3.58      ((~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['25', '26'])).
% 3.37/3.58  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('29', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('30', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('31', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 3.37/3.58  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 3.37/3.58  thf('33', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['31', '32'])).
% 3.37/3.58  thf('34', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.37/3.58         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 3.37/3.58            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.37/3.58          | ~ (v1_funct_1 @ X0))),
% 3.37/3.58      inference('demod', [status(thm)], ['24', '33'])).
% 3.37/3.58  thf('35', plain,
% 3.37/3.58      ((~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['14', '34'])).
% 3.37/3.58  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('37', plain,
% 3.37/3.58      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 3.37/3.58         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['35', '36'])).
% 3.37/3.58  thf('38', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 3.37/3.58  thf('39', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58           (k6_partfun1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('split', [status(esa)], ['1'])).
% 3.37/3.58  thf('40', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.37/3.58  thf('41', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58           (k6_relat_1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('demod', [status(thm)], ['39', '40'])).
% 3.37/3.58  thf('42', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58            sk_B) @ 
% 3.37/3.58           (k6_relat_1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['38', '41'])).
% 3.37/3.58  thf('43', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['37', '42'])).
% 3.37/3.58  thf('44', plain,
% 3.37/3.58      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 3.37/3.58            (k6_relat_1 @ sk_A))
% 3.37/3.58         | ~ (v1_relat_1 @ sk_B)
% 3.37/3.58         | ~ (v1_funct_1 @ sk_B)
% 3.37/3.58         | ~ (v2_funct_1 @ sk_B)))
% 3.37/3.58         <= (~
% 3.37/3.58             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58               (k6_partfun1 @ sk_A))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['13', '43'])).
% 3.37/3.58  thf('45', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(cc2_funct_2, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i]:
% 3.37/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.58       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 3.37/3.58         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 3.37/3.58  thf('46', plain,
% 3.37/3.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.37/3.58         (~ (v1_funct_1 @ X12)
% 3.37/3.58          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 3.37/3.58          | (v2_funct_2 @ X12 @ X14)
% 3.37/3.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.37/3.58  thf('47', plain,
% 3.37/3.58      (((v2_funct_2 @ sk_B @ sk_A)
% 3.37/3.58        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v1_funct_1 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['45', '46'])).
% 3.37/3.58  thf('48', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('50', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 3.37/3.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 3.37/3.58  thf(d3_funct_2, axiom,
% 3.37/3.58    (![A:$i,B:$i]:
% 3.37/3.58     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.37/3.58       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.37/3.58  thf('51', plain,
% 3.37/3.58      (![X15 : $i, X16 : $i]:
% 3.37/3.58         (~ (v2_funct_2 @ X16 @ X15)
% 3.37/3.58          | ((k2_relat_1 @ X16) = (X15))
% 3.37/3.58          | ~ (v5_relat_1 @ X16 @ X15)
% 3.37/3.58          | ~ (v1_relat_1 @ X16))),
% 3.37/3.58      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.37/3.58  thf('52', plain,
% 3.37/3.58      ((~ (v1_relat_1 @ sk_B)
% 3.37/3.58        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 3.37/3.58        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['50', '51'])).
% 3.37/3.58  thf('53', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(cc1_relset_1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i]:
% 3.37/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.58       ( v1_relat_1 @ C ) ))).
% 3.37/3.58  thf('54', plain,
% 3.37/3.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.37/3.58         ((v1_relat_1 @ X2)
% 3.37/3.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.37/3.58  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 3.37/3.58      inference('sup-', [status(thm)], ['53', '54'])).
% 3.37/3.58  thf('56', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(cc2_relset_1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i]:
% 3.37/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.37/3.58  thf('57', plain,
% 3.37/3.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.37/3.58         ((v5_relat_1 @ X5 @ X7)
% 3.37/3.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.37/3.58  thf('58', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 3.37/3.58      inference('sup-', [status(thm)], ['56', '57'])).
% 3.37/3.58  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 3.37/3.58      inference('demod', [status(thm)], ['52', '55', '58'])).
% 3.37/3.58  thf(dt_k6_partfun1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( m1_subset_1 @
% 3.37/3.58         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.37/3.58       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.37/3.58  thf('60', plain,
% 3.37/3.58      (![X20 : $i]:
% 3.37/3.58         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 3.37/3.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.37/3.58  thf('61', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.37/3.58  thf('62', plain,
% 3.37/3.58      (![X20 : $i]:
% 3.37/3.58         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 3.37/3.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 3.37/3.58      inference('demod', [status(thm)], ['60', '61'])).
% 3.37/3.58  thf(reflexivity_r2_relset_1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i,D:$i]:
% 3.37/3.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.37/3.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.37/3.58       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.37/3.58  thf('63', plain,
% 3.37/3.58      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.37/3.58         ((r2_relset_1 @ X8 @ X9 @ X10 @ X10)
% 3.37/3.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 3.37/3.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.37/3.58      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.37/3.58  thf('64', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.37/3.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.37/3.58      inference('condensation', [status(thm)], ['63'])).
% 3.37/3.58  thf('65', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.37/3.58      inference('sup-', [status(thm)], ['62', '64'])).
% 3.37/3.58  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 3.37/3.58      inference('sup-', [status(thm)], ['53', '54'])).
% 3.37/3.58  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('68', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('69', plain,
% 3.37/3.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.37/3.58         (~ (v1_funct_1 @ X12)
% 3.37/3.58          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 3.37/3.58          | (v2_funct_1 @ X12)
% 3.37/3.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.37/3.58  thf('70', plain,
% 3.37/3.58      (((v2_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v1_funct_1 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['68', '69'])).
% 3.37/3.58  thf('71', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('73', plain, ((v2_funct_1 @ sk_B)),
% 3.37/3.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.37/3.58  thf('74', plain,
% 3.37/3.58      (((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58         (k6_partfun1 @ sk_A)))),
% 3.37/3.58      inference('demod', [status(thm)], ['44', '59', '65', '66', '67', '73'])).
% 3.37/3.58  thf('75', plain,
% 3.37/3.58      (~
% 3.37/3.58       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58         (k6_partfun1 @ sk_A))) | 
% 3.37/3.58       ~
% 3.37/3.58       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.37/3.58          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.37/3.58         (k6_partfun1 @ sk_A)))),
% 3.37/3.58      inference('split', [status(esa)], ['1'])).
% 3.37/3.58  thf('76', plain,
% 3.37/3.58      (~
% 3.37/3.58       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.37/3.58         (k6_partfun1 @ sk_A)))),
% 3.37/3.58      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 3.37/3.58  thf('77', plain,
% 3.37/3.58      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 3.37/3.58          (k6_relat_1 @ sk_A))),
% 3.37/3.58      inference('simpl_trail', [status(thm)], ['12', '76'])).
% 3.37/3.58  thf('78', plain,
% 3.37/3.58      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 3.37/3.58  thf('79', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('80', plain,
% 3.37/3.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.37/3.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.37/3.58          | ~ (v1_funct_1 @ X21)
% 3.37/3.58          | ~ (v1_funct_1 @ X24)
% 3.37/3.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.37/3.58          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 3.37/3.58              = (k5_relat_1 @ X21 @ X24)))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.37/3.58  thf('81', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.37/3.58         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 3.37/3.58            = (k5_relat_1 @ sk_B @ X0))
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.37/3.58          | ~ (v1_funct_1 @ X0)
% 3.37/3.58          | ~ (v1_funct_1 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['79', '80'])).
% 3.37/3.58  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('83', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.37/3.58         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 3.37/3.58            = (k5_relat_1 @ sk_B @ X0))
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.37/3.58          | ~ (v1_funct_1 @ X0))),
% 3.37/3.58      inference('demod', [status(thm)], ['81', '82'])).
% 3.37/3.58  thf('84', plain,
% 3.37/3.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 3.37/3.58        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.37/3.58            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['78', '83'])).
% 3.37/3.58  thf('85', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['31', '32'])).
% 3.37/3.58  thf('86', plain,
% 3.37/3.58      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.37/3.58         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 3.37/3.58      inference('demod', [status(thm)], ['84', '85'])).
% 3.37/3.58  thf('87', plain,
% 3.37/3.58      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.37/3.58          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 3.37/3.58      inference('demod', [status(thm)], ['77', '86'])).
% 3.37/3.58  thf('88', plain,
% 3.37/3.58      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 3.37/3.58           (k6_relat_1 @ sk_A))
% 3.37/3.58        | ~ (v1_relat_1 @ sk_B)
% 3.37/3.58        | ~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v2_funct_1 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['0', '87'])).
% 3.37/3.58  thf(t55_funct_1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.37/3.58       ( ( v2_funct_1 @ A ) =>
% 3.37/3.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.37/3.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.37/3.58  thf('89', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (v2_funct_1 @ X0)
% 3.37/3.58          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.37/3.58          | ~ (v1_funct_1 @ X0)
% 3.37/3.58          | ~ (v1_relat_1 @ X0))),
% 3.37/3.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.37/3.58  thf('90', plain,
% 3.37/3.58      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 3.37/3.58  thf('91', plain,
% 3.37/3.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.37/3.58         (~ (v1_funct_1 @ X12)
% 3.37/3.58          | ~ (v3_funct_2 @ X12 @ X13 @ X14)
% 3.37/3.58          | (v2_funct_2 @ X12 @ X14)
% 3.37/3.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.37/3.58  thf('92', plain,
% 3.37/3.58      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 3.37/3.58        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['90', '91'])).
% 3.37/3.58  thf('93', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('94', plain,
% 3.37/3.58      (![X17 : $i, X18 : $i]:
% 3.37/3.58         ((v3_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 3.37/3.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 3.37/3.58          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 3.37/3.58          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 3.37/3.58          | ~ (v1_funct_1 @ X18))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 3.37/3.58  thf('95', plain,
% 3.37/3.58      ((~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.37/3.58        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['93', '94'])).
% 3.37/3.58  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('97', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('98', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('99', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 3.37/3.58  thf('100', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 3.37/3.58      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 3.37/3.58  thf('101', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['31', '32'])).
% 3.37/3.58  thf('102', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 3.37/3.58      inference('demod', [status(thm)], ['92', '100', '101'])).
% 3.37/3.58  thf('103', plain,
% 3.37/3.58      (![X15 : $i, X16 : $i]:
% 3.37/3.58         (~ (v2_funct_2 @ X16 @ X15)
% 3.37/3.58          | ((k2_relat_1 @ X16) = (X15))
% 3.37/3.58          | ~ (v5_relat_1 @ X16 @ X15)
% 3.37/3.58          | ~ (v1_relat_1 @ X16))),
% 3.37/3.58      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.37/3.58  thf('104', plain,
% 3.37/3.58      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 3.37/3.58        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 3.37/3.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['102', '103'])).
% 3.37/3.58  thf('105', plain,
% 3.37/3.58      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 3.37/3.58  thf('106', plain,
% 3.37/3.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.37/3.58         ((v1_relat_1 @ X2)
% 3.37/3.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.37/3.58  thf('107', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['105', '106'])).
% 3.37/3.58  thf('108', plain,
% 3.37/3.58      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.37/3.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.37/3.58      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 3.37/3.58  thf('109', plain,
% 3.37/3.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.37/3.58         ((v5_relat_1 @ X5 @ X7)
% 3.37/3.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.37/3.58  thf('110', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 3.37/3.58      inference('sup-', [status(thm)], ['108', '109'])).
% 3.37/3.58  thf('111', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 3.37/3.58      inference('demod', [status(thm)], ['104', '107', '110'])).
% 3.37/3.58  thf('112', plain,
% 3.37/3.58      ((((k1_relat_1 @ sk_B) = (sk_A))
% 3.37/3.58        | ~ (v1_relat_1 @ sk_B)
% 3.37/3.58        | ~ (v1_funct_1 @ sk_B)
% 3.37/3.58        | ~ (v2_funct_1 @ sk_B))),
% 3.37/3.58      inference('sup+', [status(thm)], ['89', '111'])).
% 3.37/3.58  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 3.37/3.58      inference('sup-', [status(thm)], ['53', '54'])).
% 3.37/3.58  thf('114', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('115', plain, ((v2_funct_1 @ sk_B)),
% 3.37/3.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.37/3.58  thf('116', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 3.37/3.58      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 3.37/3.58  thf('117', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.37/3.58      inference('sup-', [status(thm)], ['62', '64'])).
% 3.37/3.58  thf('118', plain, ((v1_relat_1 @ sk_B)),
% 3.37/3.58      inference('sup-', [status(thm)], ['53', '54'])).
% 3.37/3.58  thf('119', plain, ((v1_funct_1 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('120', plain, ((v2_funct_1 @ sk_B)),
% 3.37/3.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.37/3.58  thf('121', plain, ($false),
% 3.37/3.58      inference('demod', [status(thm)],
% 3.37/3.58                ['88', '116', '117', '118', '119', '120'])).
% 3.37/3.58  
% 3.37/3.58  % SZS output end Refutation
% 3.37/3.58  
% 3.37/3.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
