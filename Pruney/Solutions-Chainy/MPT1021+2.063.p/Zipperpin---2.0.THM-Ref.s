%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vL6KVBNeLm

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:21 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  240 (2769 expanded)
%              Number of leaves         :   43 ( 872 expanded)
%              Depth                    :   24
%              Number of atoms          : 2091 (60469 expanded)
%              Number of equality atoms :   84 ( 454 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ( ( k2_funct_2 @ X36 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','42'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ X13 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('46',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ X13 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k6_partfun1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k6_partfun1 @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('51',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('59',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('61',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('62',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('63',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('65',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('70',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
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
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_funct_2 @ X26 @ X25 )
      | ( ( k2_relat_1 @ X26 )
        = X25 )
      | ~ ( v5_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('79',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('81',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','57','58','59','60','61','62','81'])).

thf('83',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','82'])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('88',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('89',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('90',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('92',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','93'])).

thf('95',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('107',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('108',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('112',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('115',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('118',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('120',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('121',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X27 @ X28 ) @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('129',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('131',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['121','129','130'])).

thf('132',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_funct_2 @ X26 @ X25 )
      | ( ( k2_relat_1 @ X26 )
        = X25 )
      | ~ ( v5_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('133',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('136',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['133','134','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','79'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('140',plain,(
    ! [X38: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('143',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('146',plain,(
    v4_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('150',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('152',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('154',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('155',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('157',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['156'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('158',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X12 ) @ ( k9_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['155','159'])).

thf('161',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('162',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('164',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('166',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['118','138','164','165'])).

thf('167',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('168',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('169',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['166','171'])).

thf('173',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['118','138','164','165'])).

thf('174',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('175',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('177',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('179',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('183',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('184',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('185',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['182','185'])).

thf('187',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['118','138','164','165'])).

thf('188',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('189',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('191',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['181','191'])).

thf('193',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['97','193','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vL6KVBNeLm
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.04/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.26  % Solved by: fo/fo7.sh
% 1.04/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.26  % done 1186 iterations in 0.803s
% 1.04/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.26  % SZS output start Refutation
% 1.04/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.04/1.26  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.04/1.26  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.04/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.04/1.26  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.04/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.26  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.04/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.26  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.04/1.26  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.04/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.26  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.04/1.26  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.04/1.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.04/1.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.04/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.04/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.04/1.26  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.04/1.26  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.04/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.04/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.04/1.26  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.04/1.26  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.04/1.26  thf(t88_funct_2, conjecture,
% 1.04/1.26    (![A:$i,B:$i]:
% 1.04/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.04/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.04/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.04/1.26       ( ( r2_relset_1 @
% 1.04/1.26           A @ A @ 
% 1.04/1.26           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.04/1.26           ( k6_partfun1 @ A ) ) & 
% 1.04/1.26         ( r2_relset_1 @
% 1.04/1.26           A @ A @ 
% 1.04/1.26           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.04/1.26           ( k6_partfun1 @ A ) ) ) ))).
% 1.04/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.26    (~( ![A:$i,B:$i]:
% 1.04/1.26        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.04/1.26            ( v3_funct_2 @ B @ A @ A ) & 
% 1.04/1.26            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.04/1.26          ( ( r2_relset_1 @
% 1.04/1.26              A @ A @ 
% 1.04/1.26              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.04/1.26              ( k6_partfun1 @ A ) ) & 
% 1.04/1.26            ( r2_relset_1 @
% 1.04/1.26              A @ A @ 
% 1.04/1.26              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.04/1.26              ( k6_partfun1 @ A ) ) ) ) )),
% 1.04/1.26    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.04/1.26  thf('0', plain,
% 1.04/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.04/1.26            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.04/1.26           (k6_partfun1 @ sk_A))
% 1.04/1.26        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.04/1.26              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.04/1.26             (k6_partfun1 @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('1', plain,
% 1.04/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.04/1.26            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.04/1.26           (k6_partfun1 @ sk_A)))
% 1.04/1.26         <= (~
% 1.04/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.04/1.26                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.04/1.26               (k6_partfun1 @ sk_A))))),
% 1.04/1.26      inference('split', [status(esa)], ['0'])).
% 1.04/1.26  thf('2', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf(redefinition_k2_funct_2, axiom,
% 1.04/1.26    (![A:$i,B:$i]:
% 1.04/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.04/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.04/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.04/1.26       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.04/1.26  thf('3', plain,
% 1.04/1.26      (![X35 : $i, X36 : $i]:
% 1.04/1.26         (((k2_funct_2 @ X36 @ X35) = (k2_funct_1 @ X35))
% 1.04/1.26          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 1.04/1.26          | ~ (v3_funct_2 @ X35 @ X36 @ X36)
% 1.04/1.26          | ~ (v1_funct_2 @ X35 @ X36 @ X36)
% 1.04/1.26          | ~ (v1_funct_1 @ X35))),
% 1.04/1.26      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.04/1.26  thf('4', plain,
% 1.04/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.04/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.04/1.26      inference('sup-', [status(thm)], ['2', '3'])).
% 1.04/1.26  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.04/1.26      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.04/1.26  thf('9', plain,
% 1.04/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.04/1.26            (k2_funct_1 @ sk_B)) @ 
% 1.04/1.26           (k6_partfun1 @ sk_A)))
% 1.04/1.26         <= (~
% 1.04/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.04/1.26                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.04/1.26               (k6_partfun1 @ sk_A))))),
% 1.04/1.26      inference('demod', [status(thm)], ['1', '8'])).
% 1.04/1.26  thf('10', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('11', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf(dt_k2_funct_2, axiom,
% 1.04/1.26    (![A:$i,B:$i]:
% 1.04/1.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.04/1.26         ( v3_funct_2 @ B @ A @ A ) & 
% 1.04/1.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.04/1.26       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.04/1.26         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.04/1.26         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.04/1.26         ( m1_subset_1 @
% 1.04/1.26           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.04/1.26  thf('12', plain,
% 1.04/1.26      (![X27 : $i, X28 : $i]:
% 1.04/1.26         ((m1_subset_1 @ (k2_funct_2 @ X27 @ X28) @ 
% 1.04/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 1.04/1.26          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 1.04/1.26          | ~ (v3_funct_2 @ X28 @ X27 @ X27)
% 1.04/1.26          | ~ (v1_funct_2 @ X28 @ X27 @ X27)
% 1.04/1.26          | ~ (v1_funct_1 @ X28))),
% 1.04/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.04/1.26  thf('13', plain,
% 1.04/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.04/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.04/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.04/1.26      inference('sup-', [status(thm)], ['11', '12'])).
% 1.04/1.26  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.04/1.26      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.04/1.26  thf('18', plain,
% 1.04/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.04/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.04/1.26  thf(redefinition_k1_partfun1, axiom,
% 1.04/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.04/1.26     ( ( ( v1_funct_1 @ E ) & 
% 1.04/1.26         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.04/1.26         ( v1_funct_1 @ F ) & 
% 1.04/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.04/1.26       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.04/1.26  thf('19', plain,
% 1.04/1.26      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.04/1.26         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.04/1.26          | ~ (v1_funct_1 @ X29)
% 1.04/1.26          | ~ (v1_funct_1 @ X32)
% 1.04/1.26          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.04/1.26          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.04/1.26              = (k5_relat_1 @ X29 @ X32)))),
% 1.04/1.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.04/1.26  thf('20', plain,
% 1.04/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.04/1.26            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.04/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.04/1.26          | ~ (v1_funct_1 @ X0)
% 1.04/1.26          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.04/1.26      inference('sup-', [status(thm)], ['18', '19'])).
% 1.04/1.26  thf('21', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('22', plain,
% 1.04/1.26      (![X27 : $i, X28 : $i]:
% 1.04/1.26         ((v1_funct_1 @ (k2_funct_2 @ X27 @ X28))
% 1.04/1.26          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 1.04/1.26          | ~ (v3_funct_2 @ X28 @ X27 @ X27)
% 1.04/1.26          | ~ (v1_funct_2 @ X28 @ X27 @ X27)
% 1.04/1.26          | ~ (v1_funct_1 @ X28))),
% 1.04/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.04/1.26  thf('23', plain,
% 1.04/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.04/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.04/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.04/1.26  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('25', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('26', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('27', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.04/1.26      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 1.04/1.26  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.04/1.26      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.04/1.26  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.04/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.04/1.26  thf('30', plain,
% 1.04/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.04/1.26            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.04/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.04/1.26          | ~ (v1_funct_1 @ X0))),
% 1.04/1.26      inference('demod', [status(thm)], ['20', '29'])).
% 1.04/1.26  thf('31', plain,
% 1.04/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.04/1.26        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.04/1.26            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.04/1.26      inference('sup-', [status(thm)], ['10', '30'])).
% 1.04/1.26  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('33', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf(cc2_relset_1, axiom,
% 1.04/1.26    (![A:$i,B:$i,C:$i]:
% 1.04/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.04/1.26  thf('34', plain,
% 1.04/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.04/1.26         ((v4_relat_1 @ X14 @ X15)
% 1.04/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.04/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.04/1.26  thf('35', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 1.04/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.04/1.26  thf(t209_relat_1, axiom,
% 1.04/1.26    (![A:$i,B:$i]:
% 1.04/1.26     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.04/1.26       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.04/1.26  thf('36', plain,
% 1.04/1.26      (![X9 : $i, X10 : $i]:
% 1.04/1.26         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.04/1.26          | ~ (v4_relat_1 @ X9 @ X10)
% 1.04/1.26          | ~ (v1_relat_1 @ X9))),
% 1.04/1.26      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.04/1.26  thf('37', plain,
% 1.04/1.26      ((~ (v1_relat_1 @ sk_B) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 1.04/1.26      inference('sup-', [status(thm)], ['35', '36'])).
% 1.04/1.26  thf('38', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf(cc2_relat_1, axiom,
% 1.04/1.26    (![A:$i]:
% 1.04/1.26     ( ( v1_relat_1 @ A ) =>
% 1.04/1.26       ( ![B:$i]:
% 1.04/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.04/1.26  thf('39', plain,
% 1.04/1.26      (![X3 : $i, X4 : $i]:
% 1.04/1.26         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.04/1.26          | (v1_relat_1 @ X3)
% 1.04/1.26          | ~ (v1_relat_1 @ X4))),
% 1.04/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.04/1.26  thf('40', plain,
% 1.04/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.04/1.26      inference('sup-', [status(thm)], ['38', '39'])).
% 1.04/1.26  thf(fc6_relat_1, axiom,
% 1.04/1.26    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.04/1.26  thf('41', plain,
% 1.04/1.26      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.04/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.04/1.26  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 1.04/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.04/1.26  thf('43', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['37', '42'])).
% 1.04/1.26  thf(t148_relat_1, axiom,
% 1.04/1.26    (![A:$i,B:$i]:
% 1.04/1.26     ( ( v1_relat_1 @ B ) =>
% 1.04/1.26       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.04/1.26  thf('44', plain,
% 1.04/1.26      (![X7 : $i, X8 : $i]:
% 1.04/1.26         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.04/1.26          | ~ (v1_relat_1 @ X7))),
% 1.04/1.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.04/1.26  thf(t61_funct_1, axiom,
% 1.04/1.26    (![A:$i]:
% 1.04/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.04/1.26       ( ( v2_funct_1 @ A ) =>
% 1.04/1.26         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.04/1.26             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.04/1.26           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.04/1.26             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.04/1.26  thf('45', plain,
% 1.04/1.26      (![X13 : $i]:
% 1.04/1.26         (~ (v2_funct_1 @ X13)
% 1.04/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 1.04/1.26              = (k6_relat_1 @ (k2_relat_1 @ X13)))
% 1.04/1.26          | ~ (v1_funct_1 @ X13)
% 1.04/1.26          | ~ (v1_relat_1 @ X13))),
% 1.04/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.04/1.26  thf(redefinition_k6_partfun1, axiom,
% 1.04/1.26    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.04/1.26  thf('46', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.04/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.04/1.26  thf('47', plain,
% 1.04/1.26      (![X13 : $i]:
% 1.04/1.26         (~ (v2_funct_1 @ X13)
% 1.04/1.26          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 1.04/1.26              = (k6_partfun1 @ (k2_relat_1 @ X13)))
% 1.04/1.26          | ~ (v1_funct_1 @ X13)
% 1.04/1.26          | ~ (v1_relat_1 @ X13))),
% 1.04/1.26      inference('demod', [status(thm)], ['45', '46'])).
% 1.04/1.26  thf('48', plain,
% 1.04/1.26      (![X0 : $i, X1 : $i]:
% 1.04/1.26         (((k5_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.04/1.26            (k7_relat_1 @ X1 @ X0)) = (k6_partfun1 @ (k9_relat_1 @ X1 @ X0)))
% 1.04/1.26          | ~ (v1_relat_1 @ X1)
% 1.04/1.26          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.04/1.26          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 1.04/1.26          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.04/1.26      inference('sup+', [status(thm)], ['44', '47'])).
% 1.04/1.26  thf('49', plain,
% 1.04/1.26      ((~ (v1_relat_1 @ sk_B)
% 1.04/1.26        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 1.04/1.26        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 1.04/1.26        | ~ (v1_relat_1 @ sk_B)
% 1.04/1.26        | ((k5_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ 
% 1.04/1.26            (k7_relat_1 @ sk_B @ sk_A))
% 1.04/1.26            = (k6_partfun1 @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.04/1.26      inference('sup-', [status(thm)], ['43', '48'])).
% 1.04/1.26  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 1.04/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.04/1.26  thf('51', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['37', '42'])).
% 1.04/1.26  thf('52', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf(cc2_funct_2, axiom,
% 1.04/1.26    (![A:$i,B:$i,C:$i]:
% 1.04/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.26       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.04/1.26         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.04/1.26  thf('53', plain,
% 1.04/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.04/1.26         (~ (v1_funct_1 @ X22)
% 1.04/1.26          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 1.04/1.26          | (v2_funct_1 @ X22)
% 1.04/1.26          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.04/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.04/1.26  thf('54', plain,
% 1.04/1.26      (((v2_funct_1 @ sk_B)
% 1.04/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | ~ (v1_funct_1 @ sk_B))),
% 1.04/1.26      inference('sup-', [status(thm)], ['52', '53'])).
% 1.04/1.26  thf('55', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('57', plain, ((v2_funct_1 @ sk_B)),
% 1.04/1.26      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.04/1.26  thf('58', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['37', '42'])).
% 1.04/1.26  thf('59', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 1.04/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.04/1.26  thf('61', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['37', '42'])).
% 1.04/1.26  thf('62', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['37', '42'])).
% 1.04/1.26  thf('63', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['37', '42'])).
% 1.04/1.26  thf('64', plain,
% 1.04/1.26      (![X7 : $i, X8 : $i]:
% 1.04/1.26         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.04/1.26          | ~ (v1_relat_1 @ X7))),
% 1.04/1.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.04/1.26  thf('65', plain,
% 1.04/1.26      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 1.04/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.04/1.26      inference('sup+', [status(thm)], ['63', '64'])).
% 1.04/1.26  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 1.04/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.04/1.26  thf('67', plain, (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['65', '66'])).
% 1.04/1.26  thf('68', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('69', plain,
% 1.04/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.04/1.26         (~ (v1_funct_1 @ X22)
% 1.04/1.26          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 1.04/1.26          | (v2_funct_2 @ X22 @ X24)
% 1.04/1.26          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.04/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.04/1.26  thf('70', plain,
% 1.04/1.26      (((v2_funct_2 @ sk_B @ sk_A)
% 1.04/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.04/1.26        | ~ (v1_funct_1 @ sk_B))),
% 1.04/1.26      inference('sup-', [status(thm)], ['68', '69'])).
% 1.04/1.26  thf('71', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('73', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.04/1.26      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.04/1.26  thf(d3_funct_2, axiom,
% 1.04/1.26    (![A:$i,B:$i]:
% 1.04/1.26     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.04/1.26       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.04/1.26  thf('74', plain,
% 1.04/1.26      (![X25 : $i, X26 : $i]:
% 1.04/1.26         (~ (v2_funct_2 @ X26 @ X25)
% 1.04/1.26          | ((k2_relat_1 @ X26) = (X25))
% 1.04/1.26          | ~ (v5_relat_1 @ X26 @ X25)
% 1.04/1.26          | ~ (v1_relat_1 @ X26))),
% 1.04/1.26      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.04/1.26  thf('75', plain,
% 1.04/1.26      ((~ (v1_relat_1 @ sk_B)
% 1.04/1.26        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.04/1.26        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.04/1.26      inference('sup-', [status(thm)], ['73', '74'])).
% 1.04/1.26  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 1.04/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.04/1.26  thf('77', plain,
% 1.04/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.04/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.26  thf('78', plain,
% 1.04/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.04/1.26         ((v5_relat_1 @ X14 @ X16)
% 1.04/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.04/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.04/1.26  thf('79', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.04/1.26      inference('sup-', [status(thm)], ['77', '78'])).
% 1.04/1.26  thf('80', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.04/1.26  thf('81', plain, (((sk_A) = (k9_relat_1 @ sk_B @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['67', '80'])).
% 1.04/1.26  thf('82', plain,
% 1.04/1.26      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_partfun1 @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)],
% 1.04/1.26                ['49', '50', '51', '57', '58', '59', '60', '61', '62', '81'])).
% 1.04/1.26  thf('83', plain,
% 1.04/1.26      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.04/1.26         = (k6_partfun1 @ sk_A))),
% 1.04/1.26      inference('demod', [status(thm)], ['31', '32', '82'])).
% 1.04/1.26  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.04/1.26      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.04/1.26  thf('85', plain,
% 1.04/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.04/1.26            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.04/1.26           (k6_partfun1 @ sk_A)))
% 1.04/1.26         <= (~
% 1.04/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.04/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.04/1.26               (k6_partfun1 @ sk_A))))),
% 1.04/1.26      inference('split', [status(esa)], ['0'])).
% 1.04/1.26  thf('86', plain,
% 1.04/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.04/1.26            sk_B) @ 
% 1.04/1.26           (k6_partfun1 @ sk_A)))
% 1.04/1.26         <= (~
% 1.04/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.04/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.10/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.10/1.26               (k6_partfun1 @ sk_A))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['84', '85'])).
% 1.10/1.26  thf('87', plain,
% 1.10/1.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.10/1.26           (k6_partfun1 @ sk_A)))
% 1.10/1.26         <= (~
% 1.10/1.26             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.10/1.26                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.10/1.26               (k6_partfun1 @ sk_A))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['83', '86'])).
% 1.10/1.26  thf(t29_relset_1, axiom,
% 1.10/1.26    (![A:$i]:
% 1.10/1.26     ( m1_subset_1 @
% 1.10/1.26       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.10/1.26  thf('88', plain,
% 1.10/1.26      (![X21 : $i]:
% 1.10/1.26         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 1.10/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.10/1.26      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.10/1.26  thf('89', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.10/1.26  thf('90', plain,
% 1.10/1.26      (![X21 : $i]:
% 1.10/1.26         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.10/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.10/1.26      inference('demod', [status(thm)], ['88', '89'])).
% 1.10/1.26  thf(redefinition_r2_relset_1, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i,D:$i]:
% 1.10/1.26     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.10/1.26         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.10/1.26       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.10/1.26  thf('91', plain,
% 1.10/1.26      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.10/1.26         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.10/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.10/1.26          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 1.10/1.26          | ((X17) != (X20)))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.10/1.26  thf('92', plain,
% 1.10/1.26      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.10/1.26         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.10/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.10/1.26      inference('simplify', [status(thm)], ['91'])).
% 1.10/1.26  thf('93', plain,
% 1.10/1.26      (![X0 : $i]:
% 1.10/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.10/1.26      inference('sup-', [status(thm)], ['90', '92'])).
% 1.10/1.26  thf('94', plain,
% 1.10/1.26      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.10/1.26          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.10/1.26         (k6_partfun1 @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['87', '93'])).
% 1.10/1.26  thf('95', plain,
% 1.10/1.26      (~
% 1.10/1.26       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.10/1.26          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.10/1.26         (k6_partfun1 @ sk_A))) | 
% 1.10/1.26       ~
% 1.10/1.26       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.10/1.26          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.10/1.26         (k6_partfun1 @ sk_A)))),
% 1.10/1.26      inference('split', [status(esa)], ['0'])).
% 1.10/1.26  thf('96', plain,
% 1.10/1.26      (~
% 1.10/1.26       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.10/1.26          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.10/1.26         (k6_partfun1 @ sk_A)))),
% 1.10/1.26      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 1.10/1.26  thf('97', plain,
% 1.10/1.26      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.10/1.26          (k6_partfun1 @ sk_A))),
% 1.10/1.26      inference('simpl_trail', [status(thm)], ['9', '96'])).
% 1.10/1.26  thf('98', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.10/1.26  thf('99', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('100', plain,
% 1.10/1.26      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.10/1.26         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.10/1.26          | ~ (v1_funct_1 @ X29)
% 1.10/1.26          | ~ (v1_funct_1 @ X32)
% 1.10/1.26          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.10/1.26          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.10/1.26              = (k5_relat_1 @ X29 @ X32)))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.10/1.26  thf('101', plain,
% 1.10/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.10/1.26            = (k5_relat_1 @ sk_B @ X0))
% 1.10/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.10/1.26          | ~ (v1_funct_1 @ X0)
% 1.10/1.26          | ~ (v1_funct_1 @ sk_B))),
% 1.10/1.26      inference('sup-', [status(thm)], ['99', '100'])).
% 1.10/1.26  thf('102', plain, ((v1_funct_1 @ sk_B)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('103', plain,
% 1.10/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.26         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.10/1.26            = (k5_relat_1 @ sk_B @ X0))
% 1.10/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.10/1.26          | ~ (v1_funct_1 @ X0))),
% 1.10/1.26      inference('demod', [status(thm)], ['101', '102'])).
% 1.10/1.26  thf('104', plain,
% 1.10/1.26      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.10/1.26        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.10/1.26            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['98', '103'])).
% 1.10/1.26  thf('105', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.10/1.26  thf('106', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.10/1.26  thf('107', plain,
% 1.10/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.10/1.26         ((v4_relat_1 @ X14 @ X15)
% 1.10/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.10/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.10/1.26  thf('108', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.10/1.26      inference('sup-', [status(thm)], ['106', '107'])).
% 1.10/1.26  thf('109', plain,
% 1.10/1.26      (![X9 : $i, X10 : $i]:
% 1.10/1.26         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.10/1.26          | ~ (v4_relat_1 @ X9 @ X10)
% 1.10/1.26          | ~ (v1_relat_1 @ X9))),
% 1.10/1.26      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.10/1.26  thf('110', plain,
% 1.10/1.26      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.10/1.26        | ((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['108', '109'])).
% 1.10/1.26  thf('111', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.10/1.26  thf('112', plain,
% 1.10/1.26      (![X3 : $i, X4 : $i]:
% 1.10/1.26         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.10/1.26          | (v1_relat_1 @ X3)
% 1.10/1.26          | ~ (v1_relat_1 @ X4))),
% 1.10/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.10/1.26  thf('113', plain,
% 1.10/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.10/1.26        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['111', '112'])).
% 1.10/1.26  thf('114', plain,
% 1.10/1.26      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.10/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.10/1.26  thf('115', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['113', '114'])).
% 1.10/1.26  thf('116', plain,
% 1.10/1.26      (((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 1.10/1.26      inference('demod', [status(thm)], ['110', '115'])).
% 1.10/1.26  thf('117', plain,
% 1.10/1.26      (![X7 : $i, X8 : $i]:
% 1.10/1.26         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.10/1.26          | ~ (v1_relat_1 @ X7))),
% 1.10/1.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.10/1.26  thf('118', plain,
% 1.10/1.26      ((((k2_relat_1 @ (k2_funct_1 @ sk_B))
% 1.10/1.26          = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 1.10/1.26        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.10/1.26      inference('sup+', [status(thm)], ['116', '117'])).
% 1.10/1.26  thf('119', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.10/1.26  thf('120', plain,
% 1.10/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.10/1.26         (~ (v1_funct_1 @ X22)
% 1.10/1.26          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 1.10/1.26          | (v2_funct_2 @ X22 @ X24)
% 1.10/1.26          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.10/1.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.10/1.26  thf('121', plain,
% 1.10/1.26      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.10/1.26        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.10/1.26        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['119', '120'])).
% 1.10/1.26  thf('122', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('123', plain,
% 1.10/1.26      (![X27 : $i, X28 : $i]:
% 1.10/1.26         ((v3_funct_2 @ (k2_funct_2 @ X27 @ X28) @ X27 @ X27)
% 1.10/1.26          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 1.10/1.26          | ~ (v3_funct_2 @ X28 @ X27 @ X27)
% 1.10/1.26          | ~ (v1_funct_2 @ X28 @ X27 @ X27)
% 1.10/1.26          | ~ (v1_funct_1 @ X28))),
% 1.10/1.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.10/1.26  thf('124', plain,
% 1.10/1.26      ((~ (v1_funct_1 @ sk_B)
% 1.10/1.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.10/1.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.10/1.26        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 1.10/1.26      inference('sup-', [status(thm)], ['122', '123'])).
% 1.10/1.26  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('126', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('127', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('128', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.10/1.26  thf('129', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.10/1.26      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 1.10/1.26  thf('130', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.10/1.26  thf('131', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.10/1.26      inference('demod', [status(thm)], ['121', '129', '130'])).
% 1.10/1.26  thf('132', plain,
% 1.10/1.26      (![X25 : $i, X26 : $i]:
% 1.10/1.26         (~ (v2_funct_2 @ X26 @ X25)
% 1.10/1.26          | ((k2_relat_1 @ X26) = (X25))
% 1.10/1.26          | ~ (v5_relat_1 @ X26 @ X25)
% 1.10/1.26          | ~ (v1_relat_1 @ X26))),
% 1.10/1.26      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.10/1.26  thf('133', plain,
% 1.10/1.26      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.10/1.26        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.10/1.26        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['131', '132'])).
% 1.10/1.26  thf('134', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['113', '114'])).
% 1.10/1.26  thf('135', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.10/1.26  thf('136', plain,
% 1.10/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.10/1.26         ((v5_relat_1 @ X14 @ X16)
% 1.10/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.10/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.10/1.26  thf('137', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.10/1.26      inference('sup-', [status(thm)], ['135', '136'])).
% 1.10/1.26  thf('138', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.10/1.26      inference('demod', [status(thm)], ['133', '134', '137'])).
% 1.10/1.26  thf('139', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.10/1.26      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.10/1.26  thf(t3_funct_2, axiom,
% 1.10/1.26    (![A:$i]:
% 1.10/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.10/1.26       ( ( v1_funct_1 @ A ) & 
% 1.10/1.26         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.10/1.26         ( m1_subset_1 @
% 1.10/1.26           A @ 
% 1.10/1.26           ( k1_zfmisc_1 @
% 1.10/1.26             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.10/1.26  thf('140', plain,
% 1.10/1.26      (![X38 : $i]:
% 1.10/1.26         ((m1_subset_1 @ X38 @ 
% 1.10/1.26           (k1_zfmisc_1 @ 
% 1.10/1.26            (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))))
% 1.10/1.26          | ~ (v1_funct_1 @ X38)
% 1.10/1.26          | ~ (v1_relat_1 @ X38))),
% 1.10/1.26      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.10/1.26  thf('141', plain,
% 1.10/1.26      (((m1_subset_1 @ sk_B @ 
% 1.10/1.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.10/1.26        | ~ (v1_relat_1 @ sk_B)
% 1.10/1.26        | ~ (v1_funct_1 @ sk_B))),
% 1.10/1.26      inference('sup+', [status(thm)], ['139', '140'])).
% 1.10/1.26  thf('142', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.10/1.26  thf('143', plain, ((v1_funct_1 @ sk_B)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('144', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_B @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['141', '142', '143'])).
% 1.10/1.26  thf('145', plain,
% 1.10/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.10/1.26         ((v4_relat_1 @ X14 @ X15)
% 1.10/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.10/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.10/1.26  thf('146', plain, ((v4_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))),
% 1.10/1.26      inference('sup-', [status(thm)], ['144', '145'])).
% 1.10/1.26  thf('147', plain,
% 1.10/1.26      (![X9 : $i, X10 : $i]:
% 1.10/1.26         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.10/1.26          | ~ (v4_relat_1 @ X9 @ X10)
% 1.10/1.26          | ~ (v1_relat_1 @ X9))),
% 1.10/1.26      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.10/1.26  thf('148', plain,
% 1.10/1.26      ((~ (v1_relat_1 @ sk_B)
% 1.10/1.26        | ((sk_B) = (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['146', '147'])).
% 1.10/1.26  thf('149', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.10/1.26  thf('150', plain, (((sk_B) = (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 1.10/1.26      inference('demod', [status(thm)], ['148', '149'])).
% 1.10/1.26  thf('151', plain,
% 1.10/1.26      (![X7 : $i, X8 : $i]:
% 1.10/1.26         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.10/1.26          | ~ (v1_relat_1 @ X7))),
% 1.10/1.26      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.10/1.26  thf('152', plain,
% 1.10/1.26      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 1.10/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.26      inference('sup+', [status(thm)], ['150', '151'])).
% 1.10/1.26  thf('153', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.10/1.26      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.10/1.26  thf('154', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.10/1.26  thf('155', plain, (((sk_A) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 1.10/1.26      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.10/1.26  thf(d10_xboole_0, axiom,
% 1.10/1.26    (![A:$i,B:$i]:
% 1.10/1.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.10/1.26  thf('156', plain,
% 1.10/1.26      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.10/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.26  thf('157', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.10/1.26      inference('simplify', [status(thm)], ['156'])).
% 1.10/1.26  thf(t177_funct_1, axiom,
% 1.10/1.26    (![A:$i]:
% 1.10/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.10/1.26       ( ![B:$i]:
% 1.10/1.26         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 1.10/1.26           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 1.10/1.26             ( B ) ) ) ) ))).
% 1.10/1.26  thf('158', plain,
% 1.10/1.26      (![X11 : $i, X12 : $i]:
% 1.10/1.26         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 1.10/1.26          | ((k9_relat_1 @ (k2_funct_1 @ X12) @ (k9_relat_1 @ X12 @ X11))
% 1.10/1.26              = (X11))
% 1.10/1.26          | ~ (v2_funct_1 @ X12)
% 1.10/1.26          | ~ (v1_funct_1 @ X12)
% 1.10/1.26          | ~ (v1_relat_1 @ X12))),
% 1.10/1.26      inference('cnf', [status(esa)], [t177_funct_1])).
% 1.10/1.26  thf('159', plain,
% 1.10/1.26      (![X0 : $i]:
% 1.10/1.26         (~ (v1_relat_1 @ X0)
% 1.10/1.26          | ~ (v1_funct_1 @ X0)
% 1.10/1.26          | ~ (v2_funct_1 @ X0)
% 1.10/1.26          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.10/1.26              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['157', '158'])).
% 1.10/1.26  thf('160', plain,
% 1.10/1.26      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))
% 1.10/1.26        | ~ (v2_funct_1 @ sk_B)
% 1.10/1.26        | ~ (v1_funct_1 @ sk_B)
% 1.10/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.26      inference('sup+', [status(thm)], ['155', '159'])).
% 1.10/1.26  thf('161', plain, ((v2_funct_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.10/1.26  thf('162', plain, ((v1_funct_1 @ sk_B)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('163', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.10/1.26  thf('164', plain,
% 1.10/1.26      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 1.10/1.26  thf('165', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['113', '114'])).
% 1.10/1.26  thf('166', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['118', '138', '164', '165'])).
% 1.10/1.26  thf('167', plain,
% 1.10/1.26      (![X13 : $i]:
% 1.10/1.26         (~ (v2_funct_1 @ X13)
% 1.10/1.26          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 1.10/1.26              = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 1.10/1.26          | ~ (v1_funct_1 @ X13)
% 1.10/1.26          | ~ (v1_relat_1 @ X13))),
% 1.10/1.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.10/1.26  thf('168', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.10/1.26  thf('169', plain,
% 1.10/1.26      (![X13 : $i]:
% 1.10/1.26         (~ (v2_funct_1 @ X13)
% 1.10/1.26          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 1.10/1.26              = (k6_partfun1 @ (k1_relat_1 @ X13)))
% 1.10/1.26          | ~ (v1_funct_1 @ X13)
% 1.10/1.26          | ~ (v1_relat_1 @ X13))),
% 1.10/1.26      inference('demod', [status(thm)], ['167', '168'])).
% 1.10/1.26  thf('170', plain,
% 1.10/1.26      (![X21 : $i]:
% 1.10/1.26         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.10/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.10/1.26      inference('demod', [status(thm)], ['88', '89'])).
% 1.10/1.26  thf('171', plain,
% 1.10/1.26      (![X0 : $i]:
% 1.10/1.26         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 1.10/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.10/1.26          | ~ (v1_relat_1 @ X0)
% 1.10/1.26          | ~ (v1_funct_1 @ X0)
% 1.10/1.26          | ~ (v2_funct_1 @ X0))),
% 1.10/1.26      inference('sup+', [status(thm)], ['169', '170'])).
% 1.10/1.26  thf('172', plain,
% 1.10/1.26      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.10/1.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.10/1.26        | ~ (v2_funct_1 @ sk_B)
% 1.10/1.26        | ~ (v1_funct_1 @ sk_B)
% 1.10/1.26        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.26      inference('sup+', [status(thm)], ['166', '171'])).
% 1.10/1.26  thf('173', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['118', '138', '164', '165'])).
% 1.10/1.26  thf('174', plain, ((v2_funct_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.10/1.26  thf('175', plain, ((v1_funct_1 @ sk_B)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('176', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.10/1.26  thf('177', plain,
% 1.10/1.26      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 1.10/1.26  thf('178', plain,
% 1.10/1.26      (![X21 : $i]:
% 1.10/1.26         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.10/1.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.10/1.26      inference('demod', [status(thm)], ['88', '89'])).
% 1.10/1.26  thf('179', plain,
% 1.10/1.26      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.10/1.26         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.10/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.10/1.26          | ((X17) = (X20))
% 1.10/1.26          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.10/1.26  thf('180', plain,
% 1.10/1.26      (![X0 : $i, X1 : $i]:
% 1.10/1.26         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 1.10/1.26          | ((k6_partfun1 @ X0) = (X1))
% 1.10/1.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['178', '179'])).
% 1.10/1.26  thf('181', plain,
% 1.10/1.26      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 1.10/1.26        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.10/1.26             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['177', '180'])).
% 1.10/1.26  thf('182', plain,
% 1.10/1.26      (![X13 : $i]:
% 1.10/1.26         (~ (v2_funct_1 @ X13)
% 1.10/1.26          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 1.10/1.26              = (k6_partfun1 @ (k1_relat_1 @ X13)))
% 1.10/1.26          | ~ (v1_funct_1 @ X13)
% 1.10/1.26          | ~ (v1_relat_1 @ X13))),
% 1.10/1.26      inference('demod', [status(thm)], ['167', '168'])).
% 1.10/1.26  thf('183', plain,
% 1.10/1.26      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.10/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.10/1.26      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 1.10/1.26  thf('184', plain,
% 1.10/1.26      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.10/1.26         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.10/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.10/1.26      inference('simplify', [status(thm)], ['91'])).
% 1.10/1.26  thf('185', plain,
% 1.10/1.26      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.10/1.26        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.10/1.26        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['183', '184'])).
% 1.10/1.26  thf('186', plain,
% 1.10/1.26      (((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 1.10/1.26         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 1.10/1.26        | ~ (v1_relat_1 @ sk_B)
% 1.10/1.26        | ~ (v1_funct_1 @ sk_B)
% 1.10/1.26        | ~ (v2_funct_1 @ sk_B))),
% 1.10/1.26      inference('sup+', [status(thm)], ['182', '185'])).
% 1.10/1.26  thf('187', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 1.10/1.26      inference('demod', [status(thm)], ['118', '138', '164', '165'])).
% 1.10/1.26  thf('188', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['40', '41'])).
% 1.10/1.26  thf('189', plain, ((v1_funct_1 @ sk_B)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('190', plain, ((v2_funct_1 @ sk_B)),
% 1.10/1.26      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.10/1.26  thf('191', plain,
% 1.10/1.26      ((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.10/1.26        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.10/1.26      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 1.10/1.26  thf('192', plain,
% 1.10/1.26      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.10/1.26      inference('demod', [status(thm)], ['181', '191'])).
% 1.10/1.26  thf('193', plain,
% 1.10/1.26      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 1.10/1.26         = (k6_partfun1 @ sk_A))),
% 1.10/1.26      inference('demod', [status(thm)], ['104', '105', '192'])).
% 1.10/1.26  thf('194', plain,
% 1.10/1.26      (![X0 : $i]:
% 1.10/1.26         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.10/1.26      inference('sup-', [status(thm)], ['90', '92'])).
% 1.10/1.26  thf('195', plain, ($false),
% 1.10/1.26      inference('demod', [status(thm)], ['97', '193', '194'])).
% 1.10/1.26  
% 1.10/1.26  % SZS output end Refutation
% 1.10/1.26  
% 1.10/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
