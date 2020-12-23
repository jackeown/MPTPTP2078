%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiakBYpsOT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:23 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 548 expanded)
%              Number of leaves         :   37 ( 182 expanded)
%              Depth                    :   17
%              Number of atoms          : 1534 (12801 expanded)
%              Number of equality atoms :   39 (  83 expanded)
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
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
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
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_2 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_2 @ X17 @ X16 )
      | ( ( k2_relat_1 @ X17 )
        = X16 )
      | ~ ( v5_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['52','57','60'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('72',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','61','67','68','69','75'])).

thf('77',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('78',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('88',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','89'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('93',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v3_funct_2 @ X13 @ X14 @ X15 )
      | ( v2_funct_2 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('94',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('102',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('104',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['94','102','103'])).

thf('105',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_2 @ X17 @ X16 )
      | ( ( k2_relat_1 @ X17 )
        = X16 )
      | ~ ( v5_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('111',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('113',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('114',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['106','111','114'])).

thf('116',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('123',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['90','120','121','122','123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiakBYpsOT
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.08/2.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.08/2.29  % Solved by: fo/fo7.sh
% 2.08/2.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.08/2.29  % done 210 iterations in 1.833s
% 2.08/2.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.08/2.29  % SZS output start Refutation
% 2.08/2.29  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.08/2.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.08/2.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.08/2.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.08/2.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.08/2.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.08/2.29  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 2.08/2.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.08/2.29  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.08/2.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.08/2.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.08/2.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.08/2.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.08/2.29  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.08/2.29  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.08/2.29  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.08/2.29  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.08/2.29  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 2.08/2.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.08/2.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.08/2.29  thf(sk_B_type, type, sk_B: $i).
% 2.08/2.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.08/2.29  thf(sk_A_type, type, sk_A: $i).
% 2.08/2.29  thf(t61_funct_1, axiom,
% 2.08/2.29    (![A:$i]:
% 2.08/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.08/2.29       ( ( v2_funct_1 @ A ) =>
% 2.08/2.29         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.08/2.29             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.08/2.29           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.08/2.29             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.08/2.29  thf('0', plain,
% 2.08/2.29      (![X5 : $i]:
% 2.08/2.29         (~ (v2_funct_1 @ X5)
% 2.08/2.29          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 2.08/2.29              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 2.08/2.29          | ~ (v1_funct_1 @ X5)
% 2.08/2.29          | ~ (v1_relat_1 @ X5))),
% 2.08/2.29      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.08/2.29  thf(t88_funct_2, conjecture,
% 2.08/2.29    (![A:$i,B:$i]:
% 2.08/2.29     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.08/2.29         ( v3_funct_2 @ B @ A @ A ) & 
% 2.08/2.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.08/2.29       ( ( r2_relset_1 @
% 2.08/2.29           A @ A @ 
% 2.08/2.29           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 2.08/2.29           ( k6_partfun1 @ A ) ) & 
% 2.08/2.29         ( r2_relset_1 @
% 2.08/2.29           A @ A @ 
% 2.08/2.29           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 2.08/2.29           ( k6_partfun1 @ A ) ) ) ))).
% 2.08/2.29  thf(zf_stmt_0, negated_conjecture,
% 2.08/2.29    (~( ![A:$i,B:$i]:
% 2.08/2.29        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.08/2.29            ( v3_funct_2 @ B @ A @ A ) & 
% 2.08/2.29            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.08/2.29          ( ( r2_relset_1 @
% 2.08/2.29              A @ A @ 
% 2.08/2.29              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 2.08/2.29              ( k6_partfun1 @ A ) ) & 
% 2.08/2.29            ( r2_relset_1 @
% 2.08/2.29              A @ A @ 
% 2.08/2.29              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 2.08/2.29              ( k6_partfun1 @ A ) ) ) ) )),
% 2.08/2.29    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 2.08/2.29  thf('1', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29           (k6_partfun1 @ sk_A))
% 2.08/2.29        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29             (k6_partfun1 @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('2', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29           (k6_partfun1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('split', [status(esa)], ['1'])).
% 2.08/2.29  thf(redefinition_k6_partfun1, axiom,
% 2.08/2.29    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.08/2.29  thf('3', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.08/2.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.08/2.29  thf('4', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29           (k6_relat_1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('demod', [status(thm)], ['2', '3'])).
% 2.08/2.29  thf('5', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf(redefinition_k2_funct_2, axiom,
% 2.08/2.29    (![A:$i,B:$i]:
% 2.08/2.29     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.08/2.29         ( v3_funct_2 @ B @ A @ A ) & 
% 2.08/2.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.08/2.29       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 2.08/2.29  thf('6', plain,
% 2.08/2.29      (![X28 : $i, X29 : $i]:
% 2.08/2.29         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 2.08/2.29          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 2.08/2.29          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 2.08/2.29          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 2.08/2.29          | ~ (v1_funct_1 @ X28))),
% 2.08/2.29      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 2.08/2.29  thf('7', plain,
% 2.08/2.29      ((~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['5', '6'])).
% 2.08/2.29  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.08/2.29  thf('12', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29            (k2_funct_1 @ sk_B)) @ 
% 2.08/2.29           (k6_relat_1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('demod', [status(thm)], ['4', '11'])).
% 2.08/2.29  thf('13', plain,
% 2.08/2.29      (![X5 : $i]:
% 2.08/2.29         (~ (v2_funct_1 @ X5)
% 2.08/2.29          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 2.08/2.29              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 2.08/2.29          | ~ (v1_funct_1 @ X5)
% 2.08/2.29          | ~ (v1_relat_1 @ X5))),
% 2.08/2.29      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.08/2.29  thf('14', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('15', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf(dt_k2_funct_2, axiom,
% 2.08/2.29    (![A:$i,B:$i]:
% 2.08/2.29     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.08/2.29         ( v3_funct_2 @ B @ A @ A ) & 
% 2.08/2.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.08/2.29       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 2.08/2.29         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 2.08/2.29         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 2.08/2.29         ( m1_subset_1 @
% 2.08/2.29           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 2.08/2.29  thf('16', plain,
% 2.08/2.29      (![X18 : $i, X19 : $i]:
% 2.08/2.29         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 2.08/2.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 2.08/2.29          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 2.08/2.29          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 2.08/2.29          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 2.08/2.29          | ~ (v1_funct_1 @ X19))),
% 2.08/2.29      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 2.08/2.29  thf('17', plain,
% 2.08/2.29      ((~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 2.08/2.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.08/2.29      inference('sup-', [status(thm)], ['15', '16'])).
% 2.08/2.29  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('20', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('21', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.08/2.29  thf('22', plain,
% 2.08/2.29      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 2.08/2.29  thf(redefinition_k1_partfun1, axiom,
% 2.08/2.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.08/2.29     ( ( ( v1_funct_1 @ E ) & 
% 2.08/2.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.08/2.29         ( v1_funct_1 @ F ) & 
% 2.08/2.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.08/2.29       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.08/2.29  thf('23', plain,
% 2.08/2.29      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.08/2.29         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.08/2.29          | ~ (v1_funct_1 @ X22)
% 2.08/2.29          | ~ (v1_funct_1 @ X25)
% 2.08/2.29          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.08/2.29          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 2.08/2.29              = (k5_relat_1 @ X22 @ X25)))),
% 2.08/2.29      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.08/2.29  thf('24', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.29         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 2.08/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 2.08/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.08/2.29          | ~ (v1_funct_1 @ X0)
% 2.08/2.29          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['22', '23'])).
% 2.08/2.29  thf('25', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('26', plain,
% 2.08/2.29      (![X18 : $i, X19 : $i]:
% 2.08/2.29         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 2.08/2.29          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 2.08/2.29          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 2.08/2.29          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 2.08/2.29          | ~ (v1_funct_1 @ X19))),
% 2.08/2.29      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 2.08/2.29  thf('27', plain,
% 2.08/2.29      ((~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['25', '26'])).
% 2.08/2.29  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('29', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('30', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('31', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 2.08/2.29  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.08/2.29  thf('33', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['31', '32'])).
% 2.08/2.29  thf('34', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.29         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 2.08/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 2.08/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.08/2.29          | ~ (v1_funct_1 @ X0))),
% 2.08/2.29      inference('demod', [status(thm)], ['24', '33'])).
% 2.08/2.29  thf('35', plain,
% 2.08/2.29      ((~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['14', '34'])).
% 2.08/2.29  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('37', plain,
% 2.08/2.29      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 2.08/2.29         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['35', '36'])).
% 2.08/2.29  thf('38', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.08/2.29  thf('39', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29           (k6_partfun1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('split', [status(esa)], ['1'])).
% 2.08/2.29  thf('40', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.08/2.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.08/2.29  thf('41', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29           (k6_relat_1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.08/2.29  thf('42', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29            sk_B) @ 
% 2.08/2.29           (k6_relat_1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('sup-', [status(thm)], ['38', '41'])).
% 2.08/2.29  thf('43', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('sup-', [status(thm)], ['37', '42'])).
% 2.08/2.29  thf('44', plain,
% 2.08/2.29      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.08/2.29            (k6_relat_1 @ sk_A))
% 2.08/2.29         | ~ (v1_relat_1 @ sk_B)
% 2.08/2.29         | ~ (v1_funct_1 @ sk_B)
% 2.08/2.29         | ~ (v2_funct_1 @ sk_B)))
% 2.08/2.29         <= (~
% 2.08/2.29             ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29               (k6_partfun1 @ sk_A))))),
% 2.08/2.29      inference('sup-', [status(thm)], ['13', '43'])).
% 2.08/2.29  thf('45', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf(cc2_funct_2, axiom,
% 2.08/2.29    (![A:$i,B:$i,C:$i]:
% 2.08/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.08/2.29       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 2.08/2.29         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 2.08/2.29  thf('46', plain,
% 2.08/2.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.08/2.29         (~ (v1_funct_1 @ X13)
% 2.08/2.29          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 2.08/2.29          | (v2_funct_2 @ X13 @ X15)
% 2.08/2.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_funct_2])).
% 2.08/2.29  thf('47', plain,
% 2.08/2.29      (((v2_funct_2 @ sk_B @ sk_A)
% 2.08/2.29        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v1_funct_1 @ sk_B))),
% 2.08/2.29      inference('sup-', [status(thm)], ['45', '46'])).
% 2.08/2.29  thf('48', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('50', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 2.08/2.29      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.08/2.29  thf(d3_funct_2, axiom,
% 2.08/2.29    (![A:$i,B:$i]:
% 2.08/2.29     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.08/2.29       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.08/2.29  thf('51', plain,
% 2.08/2.29      (![X16 : $i, X17 : $i]:
% 2.08/2.29         (~ (v2_funct_2 @ X17 @ X16)
% 2.08/2.29          | ((k2_relat_1 @ X17) = (X16))
% 2.08/2.29          | ~ (v5_relat_1 @ X17 @ X16)
% 2.08/2.29          | ~ (v1_relat_1 @ X17))),
% 2.08/2.29      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.08/2.29  thf('52', plain,
% 2.08/2.29      ((~ (v1_relat_1 @ sk_B)
% 2.08/2.29        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 2.08/2.29        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['50', '51'])).
% 2.08/2.29  thf('53', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf(cc2_relat_1, axiom,
% 2.08/2.29    (![A:$i]:
% 2.08/2.29     ( ( v1_relat_1 @ A ) =>
% 2.08/2.29       ( ![B:$i]:
% 2.08/2.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.08/2.29  thf('54', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i]:
% 2.08/2.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.08/2.29          | (v1_relat_1 @ X0)
% 2.08/2.29          | ~ (v1_relat_1 @ X1))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.08/2.29  thf('55', plain,
% 2.08/2.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 2.08/2.29      inference('sup-', [status(thm)], ['53', '54'])).
% 2.08/2.29  thf(fc6_relat_1, axiom,
% 2.08/2.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.08/2.29  thf('56', plain,
% 2.08/2.29      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.08/2.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.08/2.29  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['55', '56'])).
% 2.08/2.29  thf('58', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf(cc2_relset_1, axiom,
% 2.08/2.29    (![A:$i,B:$i,C:$i]:
% 2.08/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.08/2.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.08/2.29  thf('59', plain,
% 2.08/2.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.08/2.29         ((v5_relat_1 @ X6 @ X8)
% 2.08/2.29          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.08/2.29  thf('60', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 2.08/2.29      inference('sup-', [status(thm)], ['58', '59'])).
% 2.08/2.29  thf('61', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 2.08/2.29      inference('demod', [status(thm)], ['52', '57', '60'])).
% 2.08/2.29  thf(dt_k6_partfun1, axiom,
% 2.08/2.29    (![A:$i]:
% 2.08/2.29     ( ( m1_subset_1 @
% 2.08/2.29         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.08/2.29       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.08/2.29  thf('62', plain,
% 2.08/2.29      (![X21 : $i]:
% 2.08/2.29         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 2.08/2.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.08/2.29      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.08/2.29  thf('63', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.08/2.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.08/2.29  thf('64', plain,
% 2.08/2.29      (![X21 : $i]:
% 2.08/2.29         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 2.08/2.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.08/2.29      inference('demod', [status(thm)], ['62', '63'])).
% 2.08/2.29  thf(reflexivity_r2_relset_1, axiom,
% 2.08/2.29    (![A:$i,B:$i,C:$i,D:$i]:
% 2.08/2.29     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.08/2.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.08/2.29       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 2.08/2.29  thf('65', plain,
% 2.08/2.29      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.08/2.29         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 2.08/2.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 2.08/2.29          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 2.08/2.29      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 2.08/2.29  thf('66', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.29         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.08/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.08/2.29      inference('condensation', [status(thm)], ['65'])).
% 2.08/2.29  thf('67', plain,
% 2.08/2.29      (![X0 : $i]:
% 2.08/2.29         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.08/2.29      inference('sup-', [status(thm)], ['64', '66'])).
% 2.08/2.29  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['55', '56'])).
% 2.08/2.29  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('70', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('71', plain,
% 2.08/2.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.08/2.29         (~ (v1_funct_1 @ X13)
% 2.08/2.29          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 2.08/2.29          | (v2_funct_1 @ X13)
% 2.08/2.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_funct_2])).
% 2.08/2.29  thf('72', plain,
% 2.08/2.29      (((v2_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v1_funct_1 @ sk_B))),
% 2.08/2.29      inference('sup-', [status(thm)], ['70', '71'])).
% 2.08/2.29  thf('73', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('75', plain, ((v2_funct_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['72', '73', '74'])).
% 2.08/2.29  thf('76', plain,
% 2.08/2.29      (((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29         (k6_partfun1 @ sk_A)))),
% 2.08/2.29      inference('demod', [status(thm)], ['44', '61', '67', '68', '69', '75'])).
% 2.08/2.29  thf('77', plain,
% 2.08/2.29      (~
% 2.08/2.29       ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29         (k6_partfun1 @ sk_A))) | 
% 2.08/2.29       ~
% 2.08/2.29       ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 2.08/2.29          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 2.08/2.29         (k6_partfun1 @ sk_A)))),
% 2.08/2.29      inference('split', [status(esa)], ['1'])).
% 2.08/2.29  thf('78', plain,
% 2.08/2.29      (~
% 2.08/2.29       ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 2.08/2.29         (k6_partfun1 @ sk_A)))),
% 2.08/2.29      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 2.08/2.29  thf('79', plain,
% 2.08/2.29      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 2.08/2.29          (k6_relat_1 @ sk_A))),
% 2.08/2.29      inference('simpl_trail', [status(thm)], ['12', '78'])).
% 2.08/2.29  thf('80', plain,
% 2.08/2.29      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 2.08/2.29  thf('81', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('82', plain,
% 2.08/2.29      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.08/2.29         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.08/2.29          | ~ (v1_funct_1 @ X22)
% 2.08/2.29          | ~ (v1_funct_1 @ X25)
% 2.08/2.29          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.08/2.29          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 2.08/2.29              = (k5_relat_1 @ X22 @ X25)))),
% 2.08/2.29      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.08/2.29  thf('83', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.29         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 2.08/2.29            = (k5_relat_1 @ sk_B @ X0))
% 2.08/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.08/2.29          | ~ (v1_funct_1 @ X0)
% 2.08/2.29          | ~ (v1_funct_1 @ sk_B))),
% 2.08/2.29      inference('sup-', [status(thm)], ['81', '82'])).
% 2.08/2.29  thf('84', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('85', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.08/2.29         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 2.08/2.29            = (k5_relat_1 @ sk_B @ X0))
% 2.08/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.08/2.29          | ~ (v1_funct_1 @ X0))),
% 2.08/2.29      inference('demod', [status(thm)], ['83', '84'])).
% 2.08/2.29  thf('86', plain,
% 2.08/2.29      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 2.08/2.29        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 2.08/2.29            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 2.08/2.29      inference('sup-', [status(thm)], ['80', '85'])).
% 2.08/2.29  thf('87', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['31', '32'])).
% 2.08/2.29  thf('88', plain,
% 2.08/2.29      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 2.08/2.29         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 2.08/2.29      inference('demod', [status(thm)], ['86', '87'])).
% 2.08/2.29  thf('89', plain,
% 2.08/2.29      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.08/2.29          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 2.08/2.29      inference('demod', [status(thm)], ['79', '88'])).
% 2.08/2.29  thf('90', plain,
% 2.08/2.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.08/2.29           (k6_relat_1 @ sk_A))
% 2.08/2.29        | ~ (v1_relat_1 @ sk_B)
% 2.08/2.29        | ~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v2_funct_1 @ sk_B))),
% 2.08/2.29      inference('sup-', [status(thm)], ['0', '89'])).
% 2.08/2.29  thf(t55_funct_1, axiom,
% 2.08/2.29    (![A:$i]:
% 2.08/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.08/2.29       ( ( v2_funct_1 @ A ) =>
% 2.08/2.29         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.08/2.29           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.08/2.29  thf('91', plain,
% 2.08/2.29      (![X4 : $i]:
% 2.08/2.29         (~ (v2_funct_1 @ X4)
% 2.08/2.29          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 2.08/2.29          | ~ (v1_funct_1 @ X4)
% 2.08/2.29          | ~ (v1_relat_1 @ X4))),
% 2.08/2.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.08/2.29  thf('92', plain,
% 2.08/2.29      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 2.08/2.29  thf('93', plain,
% 2.08/2.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.08/2.29         (~ (v1_funct_1 @ X13)
% 2.08/2.29          | ~ (v3_funct_2 @ X13 @ X14 @ X15)
% 2.08/2.29          | (v2_funct_2 @ X13 @ X15)
% 2.08/2.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_funct_2])).
% 2.08/2.29  thf('94', plain,
% 2.08/2.29      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 2.08/2.29        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['92', '93'])).
% 2.08/2.29  thf('95', plain,
% 2.08/2.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('96', plain,
% 2.08/2.29      (![X18 : $i, X19 : $i]:
% 2.08/2.29         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 2.08/2.29          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 2.08/2.29          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 2.08/2.29          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 2.08/2.29          | ~ (v1_funct_1 @ X19))),
% 2.08/2.29      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 2.08/2.29  thf('97', plain,
% 2.08/2.29      ((~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.08/2.29        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 2.08/2.29      inference('sup-', [status(thm)], ['95', '96'])).
% 2.08/2.29  thf('98', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('99', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('100', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('101', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 2.08/2.29  thf('102', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 2.08/2.29      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 2.08/2.29  thf('103', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['31', '32'])).
% 2.08/2.29  thf('104', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 2.08/2.29      inference('demod', [status(thm)], ['94', '102', '103'])).
% 2.08/2.29  thf('105', plain,
% 2.08/2.29      (![X16 : $i, X17 : $i]:
% 2.08/2.29         (~ (v2_funct_2 @ X17 @ X16)
% 2.08/2.29          | ((k2_relat_1 @ X17) = (X16))
% 2.08/2.29          | ~ (v5_relat_1 @ X17 @ X16)
% 2.08/2.29          | ~ (v1_relat_1 @ X17))),
% 2.08/2.29      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.08/2.29  thf('106', plain,
% 2.08/2.29      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 2.08/2.29        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 2.08/2.29        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['104', '105'])).
% 2.08/2.29  thf('107', plain,
% 2.08/2.29      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 2.08/2.29  thf('108', plain,
% 2.08/2.29      (![X0 : $i, X1 : $i]:
% 2.08/2.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.08/2.29          | (v1_relat_1 @ X0)
% 2.08/2.29          | ~ (v1_relat_1 @ X1))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.08/2.29  thf('109', plain,
% 2.08/2.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 2.08/2.29        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 2.08/2.29      inference('sup-', [status(thm)], ['107', '108'])).
% 2.08/2.29  thf('110', plain,
% 2.08/2.29      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.08/2.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.08/2.29  thf('111', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 2.08/2.29      inference('demod', [status(thm)], ['109', '110'])).
% 2.08/2.29  thf('112', plain,
% 2.08/2.29      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 2.08/2.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.08/2.29      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 2.08/2.29  thf('113', plain,
% 2.08/2.29      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.08/2.29         ((v5_relat_1 @ X6 @ X8)
% 2.08/2.29          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.08/2.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.08/2.29  thf('114', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 2.08/2.29      inference('sup-', [status(thm)], ['112', '113'])).
% 2.08/2.29  thf('115', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 2.08/2.29      inference('demod', [status(thm)], ['106', '111', '114'])).
% 2.08/2.29  thf('116', plain,
% 2.08/2.29      ((((k1_relat_1 @ sk_B) = (sk_A))
% 2.08/2.29        | ~ (v1_relat_1 @ sk_B)
% 2.08/2.29        | ~ (v1_funct_1 @ sk_B)
% 2.08/2.29        | ~ (v2_funct_1 @ sk_B))),
% 2.08/2.29      inference('sup+', [status(thm)], ['91', '115'])).
% 2.08/2.29  thf('117', plain, ((v1_relat_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['55', '56'])).
% 2.08/2.29  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('119', plain, ((v2_funct_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['72', '73', '74'])).
% 2.08/2.29  thf('120', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 2.08/2.29      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 2.08/2.29  thf('121', plain,
% 2.08/2.29      (![X0 : $i]:
% 2.08/2.29         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.08/2.29      inference('sup-', [status(thm)], ['64', '66'])).
% 2.08/2.29  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['55', '56'])).
% 2.08/2.29  thf('123', plain, ((v1_funct_1 @ sk_B)),
% 2.08/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.08/2.29  thf('124', plain, ((v2_funct_1 @ sk_B)),
% 2.08/2.29      inference('demod', [status(thm)], ['72', '73', '74'])).
% 2.08/2.29  thf('125', plain, ($false),
% 2.08/2.29      inference('demod', [status(thm)],
% 2.08/2.29                ['90', '120', '121', '122', '123', '124'])).
% 2.08/2.29  
% 2.08/2.29  % SZS output end Refutation
% 2.08/2.29  
% 2.15/2.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
