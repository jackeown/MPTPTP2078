%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9UYJ9BoMJh

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:20 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  250 (1013 expanded)
%              Number of leaves         :   46 ( 330 expanded)
%              Depth                    :   21
%              Number of atoms          : 2142 (20942 expanded)
%              Number of equality atoms :   87 ( 182 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( ( k2_funct_2 @ X40 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X40 @ X40 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X40 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
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
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('37',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('38',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('39',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('40',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('48',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_2 @ X28 @ X27 )
      | ( ( k2_relat_1 @ X28 )
        = X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['53','58','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('64',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('71',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('77',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['68','74','75','76'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','79'])).

thf('81',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('84',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['53','58','61'])).

thf('87',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('95',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','91','92','93','94'])).

thf('96',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','95'])).

thf('97',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('98',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('99',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('104',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('105',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['102','106'])).

thf('108',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('109',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('119',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','119'])).

thf('121',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('123',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('124',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('128',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('129',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('131',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','131'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('133',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('134',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('136',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('137',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X29 @ X30 ) @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('145',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('147',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['137','145','146'])).

thf('148',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_2 @ X28 @ X27 )
      | ( ( k2_relat_1 @ X28 )
        = X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('151',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('152',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('153',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['149','150','153'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['53','58','61'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('158',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('161',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('166',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('170',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('172',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('176',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('177',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('178',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('179',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('180',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('182',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('184',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['174','175','176','177','182','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['53','58','61'])).

thf('186',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['163','186'])).

thf('188',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['155'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('189',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X15 ) @ ( k9_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['187','190'])).

thf('192',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('193',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('195',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('197',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['134','154','195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('199',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('200',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('202',plain,(
    $false ),
    inference(demod,[status(thm)],['121','197','198','199','200','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9UYJ9BoMJh
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.28/1.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.28/1.52  % Solved by: fo/fo7.sh
% 1.28/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.52  % done 1501 iterations in 1.081s
% 1.28/1.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.28/1.52  % SZS output start Refutation
% 1.28/1.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.28/1.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.28/1.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.28/1.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.28/1.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.28/1.52  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.28/1.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.28/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.28/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.28/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.52  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.28/1.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.28/1.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.28/1.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.28/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.28/1.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.28/1.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.28/1.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.28/1.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.28/1.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.28/1.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.28/1.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.28/1.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.28/1.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.28/1.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.28/1.52  thf(t61_funct_1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.28/1.52       ( ( v2_funct_1 @ A ) =>
% 1.28/1.52         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.28/1.52             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.28/1.52           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.28/1.52             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.28/1.52  thf('0', plain,
% 1.28/1.52      (![X16 : $i]:
% 1.28/1.52         (~ (v2_funct_1 @ X16)
% 1.28/1.52          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 1.28/1.52              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 1.28/1.52          | ~ (v1_funct_1 @ X16)
% 1.28/1.52          | ~ (v1_relat_1 @ X16))),
% 1.28/1.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.28/1.52  thf(t88_funct_2, conjecture,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.28/1.52         ( v3_funct_2 @ B @ A @ A ) & 
% 1.28/1.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.28/1.52       ( ( r2_relset_1 @
% 1.28/1.52           A @ A @ 
% 1.28/1.52           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.28/1.52           ( k6_partfun1 @ A ) ) & 
% 1.28/1.52         ( r2_relset_1 @
% 1.28/1.52           A @ A @ 
% 1.28/1.52           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.28/1.52           ( k6_partfun1 @ A ) ) ) ))).
% 1.28/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.52    (~( ![A:$i,B:$i]:
% 1.28/1.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.28/1.52            ( v3_funct_2 @ B @ A @ A ) & 
% 1.28/1.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.28/1.52          ( ( r2_relset_1 @
% 1.28/1.52              A @ A @ 
% 1.28/1.52              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 1.28/1.52              ( k6_partfun1 @ A ) ) & 
% 1.28/1.52            ( r2_relset_1 @
% 1.28/1.52              A @ A @ 
% 1.28/1.52              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 1.28/1.52              ( k6_partfun1 @ A ) ) ) ) )),
% 1.28/1.52    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 1.28/1.52  thf('1', plain,
% 1.28/1.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.52           (k6_partfun1 @ sk_A))
% 1.28/1.52        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.52              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.52             (k6_partfun1 @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('2', plain,
% 1.28/1.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.52           (k6_partfun1 @ sk_A)))
% 1.28/1.52         <= (~
% 1.28/1.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.52               (k6_partfun1 @ sk_A))))),
% 1.28/1.52      inference('split', [status(esa)], ['1'])).
% 1.28/1.52  thf(redefinition_k6_partfun1, axiom,
% 1.28/1.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.28/1.52  thf('3', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.28/1.52  thf('4', plain,
% 1.28/1.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.52           (k6_relat_1 @ sk_A)))
% 1.28/1.52         <= (~
% 1.28/1.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.52               (k6_partfun1 @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['2', '3'])).
% 1.28/1.52  thf('5', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(redefinition_k2_funct_2, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.28/1.52         ( v3_funct_2 @ B @ A @ A ) & 
% 1.28/1.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.28/1.52       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.28/1.52  thf('6', plain,
% 1.28/1.52      (![X39 : $i, X40 : $i]:
% 1.28/1.52         (((k2_funct_2 @ X40 @ X39) = (k2_funct_1 @ X39))
% 1.28/1.52          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 1.28/1.52          | ~ (v3_funct_2 @ X39 @ X40 @ X40)
% 1.28/1.52          | ~ (v1_funct_2 @ X39 @ X40 @ X40)
% 1.28/1.52          | ~ (v1_funct_1 @ X39))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.28/1.52  thf('7', plain,
% 1.28/1.52      ((~ (v1_funct_1 @ sk_B)
% 1.28/1.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['5', '6'])).
% 1.28/1.52  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.28/1.52  thf('12', plain,
% 1.28/1.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52            (k2_funct_1 @ sk_B)) @ 
% 1.28/1.52           (k6_relat_1 @ sk_A)))
% 1.28/1.52         <= (~
% 1.28/1.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.52               (k6_partfun1 @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['4', '11'])).
% 1.28/1.52  thf('13', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('14', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(dt_k2_funct_2, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.28/1.52         ( v3_funct_2 @ B @ A @ A ) & 
% 1.28/1.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.28/1.52       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 1.28/1.52         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.28/1.52         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 1.28/1.52         ( m1_subset_1 @
% 1.28/1.52           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 1.28/1.52  thf('15', plain,
% 1.28/1.52      (![X29 : $i, X30 : $i]:
% 1.28/1.52         ((m1_subset_1 @ (k2_funct_2 @ X29 @ X30) @ 
% 1.28/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 1.28/1.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 1.28/1.52          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 1.28/1.52          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 1.28/1.52          | ~ (v1_funct_1 @ X30))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.28/1.52  thf('16', plain,
% 1.28/1.52      ((~ (v1_funct_1 @ sk_B)
% 1.28/1.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 1.28/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['14', '15'])).
% 1.28/1.52  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.28/1.52  thf('21', plain,
% 1.28/1.52      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.28/1.52  thf(redefinition_k1_partfun1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.28/1.52     ( ( ( v1_funct_1 @ E ) & 
% 1.28/1.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.28/1.52         ( v1_funct_1 @ F ) & 
% 1.28/1.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.28/1.52       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.28/1.52  thf('22', plain,
% 1.28/1.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.28/1.52         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.28/1.52          | ~ (v1_funct_1 @ X33)
% 1.28/1.52          | ~ (v1_funct_1 @ X36)
% 1.28/1.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.28/1.52          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 1.28/1.52              = (k5_relat_1 @ X33 @ X36)))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.28/1.52  thf('23', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.28/1.52            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.28/1.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.28/1.52          | ~ (v1_funct_1 @ X0)
% 1.28/1.52          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['21', '22'])).
% 1.28/1.52  thf('24', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('25', plain,
% 1.28/1.52      (![X29 : $i, X30 : $i]:
% 1.28/1.52         ((v1_funct_1 @ (k2_funct_2 @ X29 @ X30))
% 1.28/1.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 1.28/1.52          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 1.28/1.52          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 1.28/1.52          | ~ (v1_funct_1 @ X30))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.28/1.52  thf('26', plain,
% 1.28/1.52      ((~ (v1_funct_1 @ sk_B)
% 1.28/1.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 1.28/1.52  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.28/1.52  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('33', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 1.28/1.52            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 1.28/1.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.28/1.52          | ~ (v1_funct_1 @ X0))),
% 1.28/1.52      inference('demod', [status(thm)], ['23', '32'])).
% 1.28/1.52  thf('34', plain,
% 1.28/1.52      ((~ (v1_funct_1 @ sk_B)
% 1.28/1.52        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.52            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['13', '33'])).
% 1.28/1.52  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('36', plain,
% 1.28/1.52      (![X16 : $i]:
% 1.28/1.52         (~ (v2_funct_1 @ X16)
% 1.28/1.52          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 1.28/1.52              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 1.28/1.52          | ~ (v1_funct_1 @ X16)
% 1.28/1.52          | ~ (v1_relat_1 @ X16))),
% 1.28/1.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.28/1.52  thf('37', plain,
% 1.28/1.52      (![X16 : $i]:
% 1.28/1.52         (~ (v2_funct_1 @ X16)
% 1.28/1.52          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 1.28/1.52              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 1.28/1.52          | ~ (v1_funct_1 @ X16)
% 1.28/1.52          | ~ (v1_relat_1 @ X16))),
% 1.28/1.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.28/1.52  thf(dt_k6_partfun1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( m1_subset_1 @
% 1.28/1.52         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.28/1.52       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.28/1.52  thf('38', plain,
% 1.28/1.52      (![X32 : $i]:
% 1.28/1.52         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 1.28/1.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.28/1.52  thf('39', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.28/1.52  thf('40', plain,
% 1.28/1.52      (![X32 : $i]:
% 1.28/1.52         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 1.28/1.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 1.28/1.52      inference('demod', [status(thm)], ['38', '39'])).
% 1.28/1.52  thf(cc2_relat_1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ A ) =>
% 1.28/1.52       ( ![B:$i]:
% 1.28/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.28/1.52  thf('41', plain,
% 1.28/1.52      (![X3 : $i, X4 : $i]:
% 1.28/1.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.28/1.52          | (v1_relat_1 @ X3)
% 1.28/1.52          | ~ (v1_relat_1 @ X4))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.28/1.52  thf('42', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.28/1.52          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['40', '41'])).
% 1.28/1.52  thf(fc6_relat_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.28/1.52  thf('43', plain,
% 1.28/1.52      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.28/1.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.28/1.52  thf('44', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.28/1.52      inference('demod', [status(thm)], ['42', '43'])).
% 1.28/1.52  thf('45', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 1.28/1.52          | ~ (v1_relat_1 @ X0)
% 1.28/1.52          | ~ (v1_funct_1 @ X0)
% 1.28/1.52          | ~ (v2_funct_1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['37', '44'])).
% 1.28/1.52  thf('46', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(cc2_funct_2, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.28/1.52         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.28/1.52  thf('47', plain,
% 1.28/1.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.28/1.52         (~ (v1_funct_1 @ X24)
% 1.28/1.52          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 1.28/1.52          | (v2_funct_2 @ X24 @ X26)
% 1.28/1.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.28/1.52  thf('48', plain,
% 1.28/1.52      (((v2_funct_2 @ sk_B @ sk_A)
% 1.28/1.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | ~ (v1_funct_1 @ sk_B))),
% 1.28/1.52      inference('sup-', [status(thm)], ['46', '47'])).
% 1.28/1.52  thf('49', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('51', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 1.28/1.52      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.28/1.52  thf(d3_funct_2, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.28/1.52       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.28/1.52  thf('52', plain,
% 1.28/1.52      (![X27 : $i, X28 : $i]:
% 1.28/1.52         (~ (v2_funct_2 @ X28 @ X27)
% 1.28/1.52          | ((k2_relat_1 @ X28) = (X27))
% 1.28/1.52          | ~ (v5_relat_1 @ X28 @ X27)
% 1.28/1.52          | ~ (v1_relat_1 @ X28))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.28/1.52  thf('53', plain,
% 1.28/1.52      ((~ (v1_relat_1 @ sk_B)
% 1.28/1.52        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 1.28/1.52        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['51', '52'])).
% 1.28/1.52  thf('54', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('55', plain,
% 1.28/1.52      (![X3 : $i, X4 : $i]:
% 1.28/1.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.28/1.52          | (v1_relat_1 @ X3)
% 1.28/1.52          | ~ (v1_relat_1 @ X4))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.28/1.52  thf('56', plain,
% 1.28/1.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.28/1.52      inference('sup-', [status(thm)], ['54', '55'])).
% 1.28/1.52  thf('57', plain,
% 1.28/1.52      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.28/1.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.28/1.52  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.52  thf('59', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(cc2_relset_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.28/1.52  thf('60', plain,
% 1.28/1.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.28/1.52         ((v5_relat_1 @ X17 @ X19)
% 1.28/1.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.28/1.52  thf('61', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 1.28/1.52      inference('sup-', [status(thm)], ['59', '60'])).
% 1.28/1.52  thf('62', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.28/1.52      inference('demod', [status(thm)], ['53', '58', '61'])).
% 1.28/1.52  thf('63', plain,
% 1.28/1.52      (![X16 : $i]:
% 1.28/1.52         (~ (v2_funct_1 @ X16)
% 1.28/1.52          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 1.28/1.52              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 1.28/1.52          | ~ (v1_funct_1 @ X16)
% 1.28/1.52          | ~ (v1_relat_1 @ X16))),
% 1.28/1.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.28/1.52  thf('64', plain,
% 1.28/1.52      (![X32 : $i]:
% 1.28/1.52         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 1.28/1.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 1.28/1.52      inference('demod', [status(thm)], ['38', '39'])).
% 1.28/1.52  thf('65', plain,
% 1.28/1.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.28/1.52         ((v4_relat_1 @ X17 @ X18)
% 1.28/1.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.28/1.52  thf('66', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 1.28/1.52      inference('sup-', [status(thm)], ['64', '65'])).
% 1.28/1.52  thf('67', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 1.28/1.52           (k2_relat_1 @ X0))
% 1.28/1.52          | ~ (v1_relat_1 @ X0)
% 1.28/1.52          | ~ (v1_funct_1 @ X0)
% 1.28/1.52          | ~ (v2_funct_1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['63', '66'])).
% 1.28/1.52  thf('68', plain,
% 1.28/1.52      (((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 1.28/1.52        | ~ (v2_funct_1 @ sk_B)
% 1.28/1.52        | ~ (v1_funct_1 @ sk_B)
% 1.28/1.52        | ~ (v1_relat_1 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['62', '67'])).
% 1.28/1.52  thf('69', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('70', plain,
% 1.28/1.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.28/1.52         (~ (v1_funct_1 @ X24)
% 1.28/1.52          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 1.28/1.52          | (v2_funct_1 @ X24)
% 1.28/1.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.28/1.52  thf('71', plain,
% 1.28/1.52      (((v2_funct_1 @ sk_B)
% 1.28/1.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.52        | ~ (v1_funct_1 @ sk_B))),
% 1.28/1.52      inference('sup-', [status(thm)], ['69', '70'])).
% 1.28/1.52  thf('72', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 1.28/1.52      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.28/1.52  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.52  thf('77', plain,
% 1.28/1.52      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)),
% 1.28/1.52      inference('demod', [status(thm)], ['68', '74', '75', '76'])).
% 1.28/1.53  thf(t209_relat_1, axiom,
% 1.28/1.53    (![A:$i,B:$i]:
% 1.28/1.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.28/1.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.28/1.53  thf('78', plain,
% 1.28/1.53      (![X10 : $i, X11 : $i]:
% 1.28/1.53         (((X10) = (k7_relat_1 @ X10 @ X11))
% 1.28/1.53          | ~ (v4_relat_1 @ X10 @ X11)
% 1.28/1.53          | ~ (v1_relat_1 @ X10))),
% 1.28/1.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.28/1.53  thf('79', plain,
% 1.28/1.53      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 1.28/1.53        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.28/1.53            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['77', '78'])).
% 1.28/1.53  thf('80', plain,
% 1.28/1.53      ((~ (v2_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.28/1.53        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.28/1.53            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['45', '79'])).
% 1.28/1.53  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.28/1.53  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('84', plain,
% 1.28/1.53      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.28/1.53         = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 1.28/1.53  thf('85', plain,
% 1.28/1.53      ((((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.28/1.53          = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A))
% 1.28/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.28/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v2_funct_1 @ sk_B))),
% 1.28/1.53      inference('sup+', [status(thm)], ['36', '84'])).
% 1.28/1.53  thf('86', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['53', '58', '61'])).
% 1.28/1.53  thf('87', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 1.28/1.53      inference('sup-', [status(thm)], ['64', '65'])).
% 1.28/1.53  thf('88', plain,
% 1.28/1.53      (![X10 : $i, X11 : $i]:
% 1.28/1.53         (((X10) = (k7_relat_1 @ X10 @ X11))
% 1.28/1.53          | ~ (v4_relat_1 @ X10 @ X11)
% 1.28/1.53          | ~ (v1_relat_1 @ X10))),
% 1.28/1.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.28/1.53  thf('89', plain,
% 1.28/1.53      (![X0 : $i]:
% 1.28/1.53         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.28/1.53          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['87', '88'])).
% 1.28/1.53  thf('90', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.28/1.53      inference('demod', [status(thm)], ['42', '43'])).
% 1.28/1.53  thf('91', plain,
% 1.28/1.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 1.28/1.53      inference('demod', [status(thm)], ['89', '90'])).
% 1.28/1.53  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('94', plain, ((v2_funct_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.28/1.53  thf('95', plain,
% 1.28/1.53      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['85', '86', '91', '92', '93', '94'])).
% 1.28/1.53  thf('96', plain,
% 1.28/1.53      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.28/1.53         = (k6_relat_1 @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['34', '35', '95'])).
% 1.28/1.53  thf('97', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.28/1.53  thf('98', plain,
% 1.28/1.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53           (k6_partfun1 @ sk_A)))
% 1.28/1.53         <= (~
% 1.28/1.53             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53               (k6_partfun1 @ sk_A))))),
% 1.28/1.53      inference('split', [status(esa)], ['1'])).
% 1.28/1.53  thf('99', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 1.28/1.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.28/1.53  thf('100', plain,
% 1.28/1.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53           (k6_relat_1 @ sk_A)))
% 1.28/1.53         <= (~
% 1.28/1.53             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53               (k6_partfun1 @ sk_A))))),
% 1.28/1.53      inference('demod', [status(thm)], ['98', '99'])).
% 1.28/1.53  thf('101', plain,
% 1.28/1.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.53            sk_B) @ 
% 1.28/1.53           (k6_relat_1 @ sk_A)))
% 1.28/1.53         <= (~
% 1.28/1.53             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53               (k6_partfun1 @ sk_A))))),
% 1.28/1.53      inference('sup-', [status(thm)], ['97', '100'])).
% 1.28/1.53  thf('102', plain,
% 1.28/1.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.28/1.53           (k6_relat_1 @ sk_A)))
% 1.28/1.53         <= (~
% 1.28/1.53             ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53               (k6_partfun1 @ sk_A))))),
% 1.28/1.53      inference('sup-', [status(thm)], ['96', '101'])).
% 1.28/1.53  thf('103', plain,
% 1.28/1.53      (![X32 : $i]:
% 1.28/1.53         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 1.28/1.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 1.28/1.53      inference('demod', [status(thm)], ['38', '39'])).
% 1.28/1.53  thf(redefinition_r2_relset_1, axiom,
% 1.28/1.53    (![A:$i,B:$i,C:$i,D:$i]:
% 1.28/1.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.28/1.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.28/1.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.28/1.53  thf('104', plain,
% 1.28/1.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.28/1.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.28/1.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.28/1.53          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 1.28/1.53          | ((X20) != (X23)))),
% 1.28/1.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.28/1.53  thf('105', plain,
% 1.28/1.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.28/1.53         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 1.28/1.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.28/1.53      inference('simplify', [status(thm)], ['104'])).
% 1.28/1.53  thf('106', plain,
% 1.28/1.53      (![X0 : $i]:
% 1.28/1.53         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.28/1.53      inference('sup-', [status(thm)], ['103', '105'])).
% 1.28/1.53  thf('107', plain,
% 1.28/1.53      (((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53         (k6_partfun1 @ sk_A)))),
% 1.28/1.53      inference('demod', [status(thm)], ['102', '106'])).
% 1.28/1.53  thf('108', plain,
% 1.28/1.53      (~
% 1.28/1.53       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.53          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.53         (k6_partfun1 @ sk_A))) | 
% 1.28/1.53       ~
% 1.28/1.53       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 1.28/1.53          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 1.28/1.53         (k6_partfun1 @ sk_A)))),
% 1.28/1.53      inference('split', [status(esa)], ['1'])).
% 1.28/1.53  thf('109', plain,
% 1.28/1.53      (~
% 1.28/1.53       ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.53          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 1.28/1.53         (k6_partfun1 @ sk_A)))),
% 1.28/1.53      inference('sat_resolution*', [status(thm)], ['107', '108'])).
% 1.28/1.53  thf('110', plain,
% 1.28/1.53      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 1.28/1.53          (k6_relat_1 @ sk_A))),
% 1.28/1.53      inference('simpl_trail', [status(thm)], ['12', '109'])).
% 1.28/1.53  thf('111', plain,
% 1.28/1.53      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.28/1.53  thf('112', plain,
% 1.28/1.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('113', plain,
% 1.28/1.53      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.28/1.53         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.28/1.53          | ~ (v1_funct_1 @ X33)
% 1.28/1.53          | ~ (v1_funct_1 @ X36)
% 1.28/1.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.28/1.53          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 1.28/1.53              = (k5_relat_1 @ X33 @ X36)))),
% 1.28/1.53      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.28/1.53  thf('114', plain,
% 1.28/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.53         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.28/1.53            = (k5_relat_1 @ sk_B @ X0))
% 1.28/1.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.28/1.53          | ~ (v1_funct_1 @ X0)
% 1.28/1.53          | ~ (v1_funct_1 @ sk_B))),
% 1.28/1.53      inference('sup-', [status(thm)], ['112', '113'])).
% 1.28/1.53  thf('115', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('116', plain,
% 1.28/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.53         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 1.28/1.53            = (k5_relat_1 @ sk_B @ X0))
% 1.28/1.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.28/1.53          | ~ (v1_funct_1 @ X0))),
% 1.28/1.53      inference('demod', [status(thm)], ['114', '115'])).
% 1.28/1.53  thf('117', plain,
% 1.28/1.53      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.28/1.53        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 1.28/1.53            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 1.28/1.53      inference('sup-', [status(thm)], ['111', '116'])).
% 1.28/1.53  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['30', '31'])).
% 1.28/1.53  thf('119', plain,
% 1.28/1.53      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 1.28/1.53         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 1.28/1.53      inference('demod', [status(thm)], ['117', '118'])).
% 1.28/1.53  thf('120', plain,
% 1.28/1.53      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.28/1.53          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['110', '119'])).
% 1.28/1.53  thf('121', plain,
% 1.28/1.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 1.28/1.53           (k6_relat_1 @ sk_A))
% 1.28/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.28/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v2_funct_1 @ sk_B))),
% 1.28/1.53      inference('sup-', [status(thm)], ['0', '120'])).
% 1.28/1.53  thf('122', plain,
% 1.28/1.53      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.28/1.53  thf('123', plain,
% 1.28/1.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.28/1.53         ((v4_relat_1 @ X17 @ X18)
% 1.28/1.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.28/1.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.28/1.53  thf('124', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.28/1.53      inference('sup-', [status(thm)], ['122', '123'])).
% 1.28/1.53  thf('125', plain,
% 1.28/1.53      (![X10 : $i, X11 : $i]:
% 1.28/1.53         (((X10) = (k7_relat_1 @ X10 @ X11))
% 1.28/1.53          | ~ (v4_relat_1 @ X10 @ X11)
% 1.28/1.53          | ~ (v1_relat_1 @ X10))),
% 1.28/1.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.28/1.53  thf('126', plain,
% 1.28/1.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.28/1.53        | ((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['124', '125'])).
% 1.28/1.53  thf('127', plain,
% 1.28/1.53      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.28/1.53  thf('128', plain,
% 1.28/1.53      (![X3 : $i, X4 : $i]:
% 1.28/1.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.28/1.53          | (v1_relat_1 @ X3)
% 1.28/1.53          | ~ (v1_relat_1 @ X4))),
% 1.28/1.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.28/1.53  thf('129', plain,
% 1.28/1.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.28/1.53        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['127', '128'])).
% 1.28/1.53  thf('130', plain,
% 1.28/1.53      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.28/1.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.28/1.53  thf('131', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['129', '130'])).
% 1.28/1.53  thf('132', plain,
% 1.28/1.53      (((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['126', '131'])).
% 1.28/1.53  thf(t148_relat_1, axiom,
% 1.28/1.53    (![A:$i,B:$i]:
% 1.28/1.53     ( ( v1_relat_1 @ B ) =>
% 1.28/1.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.28/1.53  thf('133', plain,
% 1.28/1.53      (![X7 : $i, X8 : $i]:
% 1.28/1.53         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.28/1.53          | ~ (v1_relat_1 @ X7))),
% 1.28/1.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.28/1.53  thf('134', plain,
% 1.28/1.53      ((((k2_relat_1 @ (k2_funct_1 @ sk_B))
% 1.28/1.53          = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 1.28/1.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.28/1.53      inference('sup+', [status(thm)], ['132', '133'])).
% 1.28/1.53  thf('135', plain,
% 1.28/1.53      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.28/1.53  thf('136', plain,
% 1.28/1.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.28/1.53         (~ (v1_funct_1 @ X24)
% 1.28/1.53          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 1.28/1.53          | (v2_funct_2 @ X24 @ X26)
% 1.28/1.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.28/1.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.28/1.53  thf('137', plain,
% 1.28/1.53      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.28/1.53        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 1.28/1.53        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['135', '136'])).
% 1.28/1.53  thf('138', plain,
% 1.28/1.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('139', plain,
% 1.28/1.53      (![X29 : $i, X30 : $i]:
% 1.28/1.53         ((v3_funct_2 @ (k2_funct_2 @ X29 @ X30) @ X29 @ X29)
% 1.28/1.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 1.28/1.53          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 1.28/1.53          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 1.28/1.53          | ~ (v1_funct_1 @ X30))),
% 1.28/1.53      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 1.28/1.53  thf('140', plain,
% 1.28/1.53      ((~ (v1_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.28/1.53        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 1.28/1.53      inference('sup-', [status(thm)], ['138', '139'])).
% 1.28/1.53  thf('141', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('142', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('143', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('144', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.28/1.53  thf('145', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 1.28/1.53      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 1.28/1.53  thf('146', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['30', '31'])).
% 1.28/1.53  thf('147', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.28/1.53      inference('demod', [status(thm)], ['137', '145', '146'])).
% 1.28/1.53  thf('148', plain,
% 1.28/1.53      (![X27 : $i, X28 : $i]:
% 1.28/1.53         (~ (v2_funct_2 @ X28 @ X27)
% 1.28/1.53          | ((k2_relat_1 @ X28) = (X27))
% 1.28/1.53          | ~ (v5_relat_1 @ X28 @ X27)
% 1.28/1.53          | ~ (v1_relat_1 @ X28))),
% 1.28/1.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.28/1.53  thf('149', plain,
% 1.28/1.53      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.28/1.53        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 1.28/1.53        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['147', '148'])).
% 1.28/1.53  thf('150', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['129', '130'])).
% 1.28/1.53  thf('151', plain,
% 1.28/1.53      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 1.28/1.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 1.28/1.53  thf('152', plain,
% 1.28/1.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.28/1.53         ((v5_relat_1 @ X17 @ X19)
% 1.28/1.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.28/1.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.28/1.53  thf('153', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 1.28/1.53      inference('sup-', [status(thm)], ['151', '152'])).
% 1.28/1.53  thf('154', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['149', '150', '153'])).
% 1.28/1.53  thf(d10_xboole_0, axiom,
% 1.28/1.53    (![A:$i,B:$i]:
% 1.28/1.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.28/1.53  thf('155', plain,
% 1.28/1.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.28/1.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.28/1.53  thf('156', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.28/1.53      inference('simplify', [status(thm)], ['155'])).
% 1.28/1.53  thf('157', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['53', '58', '61'])).
% 1.28/1.53  thf(t147_funct_1, axiom,
% 1.28/1.53    (![A:$i,B:$i]:
% 1.28/1.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.28/1.53       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.28/1.53         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.28/1.53  thf('158', plain,
% 1.28/1.53      (![X12 : $i, X13 : $i]:
% 1.28/1.53         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 1.28/1.53          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 1.28/1.53          | ~ (v1_funct_1 @ X13)
% 1.28/1.53          | ~ (v1_relat_1 @ X13))),
% 1.28/1.53      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.28/1.53  thf('159', plain,
% 1.28/1.53      (![X0 : $i]:
% 1.28/1.53         (~ (r1_tarski @ X0 @ sk_A)
% 1.28/1.53          | ~ (v1_relat_1 @ sk_B)
% 1.28/1.53          | ~ (v1_funct_1 @ sk_B)
% 1.28/1.53          | ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)) = (X0)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['157', '158'])).
% 1.28/1.53  thf('160', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('161', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('162', plain,
% 1.28/1.53      (![X0 : $i]:
% 1.28/1.53         (~ (r1_tarski @ X0 @ sk_A)
% 1.28/1.53          | ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)) = (X0)))),
% 1.28/1.53      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.28/1.53  thf('163', plain,
% 1.28/1.53      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.28/1.53      inference('sup-', [status(thm)], ['156', '162'])).
% 1.28/1.53  thf('164', plain,
% 1.28/1.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('165', plain,
% 1.28/1.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.28/1.53         ((v4_relat_1 @ X17 @ X18)
% 1.28/1.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.28/1.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.28/1.53  thf('166', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 1.28/1.53      inference('sup-', [status(thm)], ['164', '165'])).
% 1.28/1.53  thf('167', plain,
% 1.28/1.53      (![X10 : $i, X11 : $i]:
% 1.28/1.53         (((X10) = (k7_relat_1 @ X10 @ X11))
% 1.28/1.53          | ~ (v4_relat_1 @ X10 @ X11)
% 1.28/1.53          | ~ (v1_relat_1 @ X10))),
% 1.28/1.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.28/1.53  thf('168', plain,
% 1.28/1.53      ((~ (v1_relat_1 @ sk_B) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['166', '167'])).
% 1.28/1.53  thf('169', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('170', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['168', '169'])).
% 1.28/1.53  thf('171', plain,
% 1.28/1.53      (![X7 : $i, X8 : $i]:
% 1.28/1.53         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.28/1.53          | ~ (v1_relat_1 @ X7))),
% 1.28/1.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.28/1.53  thf(t169_relat_1, axiom,
% 1.28/1.53    (![A:$i]:
% 1.28/1.53     ( ( v1_relat_1 @ A ) =>
% 1.28/1.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.28/1.53  thf('172', plain,
% 1.28/1.53      (![X9 : $i]:
% 1.28/1.53         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 1.28/1.53          | ~ (v1_relat_1 @ X9))),
% 1.28/1.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.28/1.53  thf('173', plain,
% 1.28/1.53      (![X0 : $i, X1 : $i]:
% 1.28/1.53         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.28/1.53            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.28/1.53          | ~ (v1_relat_1 @ X1)
% 1.28/1.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.28/1.53      inference('sup+', [status(thm)], ['171', '172'])).
% 1.28/1.53  thf('174', plain,
% 1.28/1.53      ((~ (v1_relat_1 @ sk_B)
% 1.28/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.28/1.53        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.28/1.53            (k9_relat_1 @ sk_B @ sk_A))
% 1.28/1.53            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.28/1.53      inference('sup-', [status(thm)], ['170', '173'])).
% 1.28/1.53  thf('175', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('176', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('177', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['168', '169'])).
% 1.28/1.53  thf('178', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['168', '169'])).
% 1.28/1.53  thf('179', plain,
% 1.28/1.53      (![X7 : $i, X8 : $i]:
% 1.28/1.53         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.28/1.53          | ~ (v1_relat_1 @ X7))),
% 1.28/1.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.28/1.53  thf('180', plain,
% 1.28/1.53      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 1.28/1.53        | ~ (v1_relat_1 @ sk_B))),
% 1.28/1.53      inference('sup+', [status(thm)], ['178', '179'])).
% 1.28/1.53  thf('181', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('182', plain, (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['180', '181'])).
% 1.28/1.53  thf('183', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['168', '169'])).
% 1.28/1.53  thf('184', plain,
% 1.28/1.53      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)],
% 1.28/1.53                ['174', '175', '176', '177', '182', '183'])).
% 1.28/1.53  thf('185', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['53', '58', '61'])).
% 1.28/1.53  thf('186', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['184', '185'])).
% 1.28/1.53  thf('187', plain, (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.28/1.53      inference('demod', [status(thm)], ['163', '186'])).
% 1.28/1.53  thf('188', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.28/1.53      inference('simplify', [status(thm)], ['155'])).
% 1.28/1.53  thf(t177_funct_1, axiom,
% 1.28/1.53    (![A:$i]:
% 1.28/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.28/1.53       ( ![B:$i]:
% 1.28/1.53         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 1.28/1.53           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 1.28/1.53             ( B ) ) ) ) ))).
% 1.28/1.53  thf('189', plain,
% 1.28/1.53      (![X14 : $i, X15 : $i]:
% 1.28/1.53         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 1.28/1.53          | ((k9_relat_1 @ (k2_funct_1 @ X15) @ (k9_relat_1 @ X15 @ X14))
% 1.28/1.53              = (X14))
% 1.28/1.53          | ~ (v2_funct_1 @ X15)
% 1.28/1.53          | ~ (v1_funct_1 @ X15)
% 1.28/1.53          | ~ (v1_relat_1 @ X15))),
% 1.28/1.53      inference('cnf', [status(esa)], [t177_funct_1])).
% 1.28/1.53  thf('190', plain,
% 1.28/1.53      (![X0 : $i]:
% 1.28/1.53         (~ (v1_relat_1 @ X0)
% 1.28/1.53          | ~ (v1_funct_1 @ X0)
% 1.28/1.53          | ~ (v2_funct_1 @ X0)
% 1.28/1.53          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.28/1.53              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 1.28/1.53      inference('sup-', [status(thm)], ['188', '189'])).
% 1.28/1.53  thf('191', plain,
% 1.28/1.53      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))
% 1.28/1.53        | ~ (v2_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.28/1.53        | ~ (v1_relat_1 @ sk_B))),
% 1.28/1.53      inference('sup+', [status(thm)], ['187', '190'])).
% 1.28/1.53  thf('192', plain, ((v2_funct_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.28/1.53  thf('193', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('194', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('195', plain,
% 1.28/1.53      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 1.28/1.53  thf('196', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['129', '130'])).
% 1.28/1.53  thf('197', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 1.28/1.53      inference('demod', [status(thm)], ['134', '154', '195', '196'])).
% 1.28/1.53  thf('198', plain,
% 1.28/1.53      (![X0 : $i]:
% 1.28/1.53         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.28/1.53      inference('sup-', [status(thm)], ['103', '105'])).
% 1.28/1.53  thf('199', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['56', '57'])).
% 1.28/1.53  thf('200', plain, ((v1_funct_1 @ sk_B)),
% 1.28/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.53  thf('201', plain, ((v2_funct_1 @ sk_B)),
% 1.28/1.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.28/1.53  thf('202', plain, ($false),
% 1.28/1.53      inference('demod', [status(thm)],
% 1.28/1.53                ['121', '197', '198', '199', '200', '201'])).
% 1.28/1.53  
% 1.28/1.53  % SZS output end Refutation
% 1.28/1.53  
% 1.36/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
