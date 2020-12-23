%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uhEa0WOGQR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:21 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  250 (1013 expanded)
%              Number of leaves         :   46 ( 330 expanded)
%              Depth                    :   21
%              Number of atoms          : 2136 (20930 expanded)
%              Number of equality atoms :   85 ( 178 expanded)
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

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('104',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['104'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uhEa0WOGQR
% 0.13/0.37  % Computer   : n023.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.37  % CPULimit   : 60
% 0.21/0.37  % DateTime   : Tue Dec  1 20:44:36 EST 2020
% 0.21/0.37  % CPUTime    : 
% 0.21/0.37  % Running portfolio for 600 s
% 0.21/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.37  % Number of cores: 8
% 0.21/0.37  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 0.79/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/1.01  % Solved by: fo/fo7.sh
% 0.79/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.01  % done 848 iterations in 0.556s
% 0.79/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/1.01  % SZS output start Refutation
% 0.79/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/1.01  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.79/1.01  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.79/1.01  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.79/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.01  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.79/1.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.79/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.01  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.79/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.79/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.79/1.01  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.79/1.01  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.79/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.79/1.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.79/1.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/1.01  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.79/1.01  thf(t61_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_1 @ A ) =>
% 0.79/1.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.79/1.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.79/1.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.79/1.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('0', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 0.79/1.01              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf(t88_funct_2, conjecture,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.79/1.01         ( v3_funct_2 @ B @ A @ A ) & 
% 0.79/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.79/1.01       ( ( r2_relset_1 @
% 0.79/1.01           A @ A @ 
% 0.79/1.01           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.79/1.01           ( k6_partfun1 @ A ) ) & 
% 0.79/1.01         ( r2_relset_1 @
% 0.79/1.01           A @ A @ 
% 0.79/1.01           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.79/1.01           ( k6_partfun1 @ A ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.01    (~( ![A:$i,B:$i]:
% 0.79/1.01        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.79/1.01            ( v3_funct_2 @ B @ A @ A ) & 
% 0.79/1.01            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.79/1.01          ( ( r2_relset_1 @
% 0.79/1.01              A @ A @ 
% 0.79/1.01              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.79/1.01              ( k6_partfun1 @ A ) ) & 
% 0.79/1.01            ( r2_relset_1 @
% 0.79/1.01              A @ A @ 
% 0.79/1.01              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.79/1.01              ( k6_partfun1 @ A ) ) ) ) )),
% 0.79/1.01    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.79/1.01  thf('1', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A))
% 0.79/1.01        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01             (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('2', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('split', [status(esa)], ['1'])).
% 0.79/1.01  thf(redefinition_k6_partfun1, axiom,
% 0.79/1.01    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.79/1.01  thf('3', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('4', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01           (k6_relat_1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('demod', [status(thm)], ['2', '3'])).
% 0.79/1.01  thf('5', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(redefinition_k2_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.79/1.01         ( v3_funct_2 @ B @ A @ A ) & 
% 0.79/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.79/1.01       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.79/1.01  thf('6', plain,
% 0.79/1.01      (![X39 : $i, X40 : $i]:
% 0.79/1.01         (((k2_funct_2 @ X40 @ X39) = (k2_funct_1 @ X39))
% 0.79/1.01          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 0.79/1.01          | ~ (v3_funct_2 @ X39 @ X40 @ X40)
% 0.79/1.01          | ~ (v1_funct_2 @ X39 @ X40 @ X40)
% 0.79/1.01          | ~ (v1_funct_1 @ X39))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.79/1.01  thf('7', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['5', '6'])).
% 0.79/1.01  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.79/1.01  thf('12', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01            (k2_funct_1 @ sk_B)) @ 
% 0.79/1.01           (k6_relat_1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('demod', [status(thm)], ['4', '11'])).
% 0.79/1.01  thf('13', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('14', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(dt_k2_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.79/1.01         ( v3_funct_2 @ B @ A @ A ) & 
% 0.79/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.79/1.01       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.79/1.01         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.79/1.01         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.79/1.01         ( m1_subset_1 @
% 0.79/1.01           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.79/1.01  thf('15', plain,
% 0.79/1.01      (![X29 : $i, X30 : $i]:
% 0.79/1.01         ((m1_subset_1 @ (k2_funct_2 @ X29 @ X30) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.79/1.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.79/1.01          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 0.79/1.01          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.79/1.01          | ~ (v1_funct_1 @ X30))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.79/1.01  thf('16', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/1.01  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.79/1.01  thf('21', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.79/1.01  thf(redefinition_k1_partfun1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_1 @ F ) & 
% 0.79/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/1.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.79/1.01  thf('22', plain,
% 0.79/1.01      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.79/1.01          | ~ (v1_funct_1 @ X33)
% 0.79/1.01          | ~ (v1_funct_1 @ X36)
% 0.79/1.01          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.79/1.01          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 0.79/1.01              = (k5_relat_1 @ X33 @ X36)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/1.01  thf('23', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.79/1.01            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/1.01  thf('24', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('25', plain,
% 0.79/1.01      (![X29 : $i, X30 : $i]:
% 0.79/1.01         ((v1_funct_1 @ (k2_funct_2 @ X29 @ X30))
% 0.79/1.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.79/1.01          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 0.79/1.01          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.79/1.01          | ~ (v1_funct_1 @ X30))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.79/1.01  thf('26', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['24', '25'])).
% 0.79/1.01  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('30', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.79/1.01  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.79/1.01  thf('32', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.79/1.01  thf('33', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.79/1.01            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '32'])).
% 0.79/1.01  thf('34', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['13', '33'])).
% 0.79/1.01  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('36', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('37', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf(dt_k6_partfun1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( m1_subset_1 @
% 0.79/1.01         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.79/1.01       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.79/1.01  thf('38', plain,
% 0.79/1.01      (![X32 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.79/1.01  thf('39', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('40', plain,
% 0.79/1.01      (![X32 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.79/1.01  thf(cc2_relat_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v1_relat_1 @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.79/1.01  thf('41', plain,
% 0.79/1.01      (![X3 : $i, X4 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/1.01          | (v1_relat_1 @ X3)
% 0.79/1.01          | ~ (v1_relat_1 @ X4))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/1.01  thf('42', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.79/1.01          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['40', '41'])).
% 0.79/1.01  thf(fc6_relat_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.79/1.01  thf('43', plain,
% 0.79/1.01      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/1.01  thf('44', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['42', '43'])).
% 0.79/1.01  thf('45', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['37', '44'])).
% 0.79/1.01  thf('46', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(cc2_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.01       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.79/1.01         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.79/1.01  thf('47', plain,
% 0.79/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X24)
% 0.79/1.01          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.79/1.01          | (v2_funct_2 @ X24 @ X26)
% 0.79/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.79/1.01  thf('48', plain,
% 0.79/1.01      (((v2_funct_2 @ sk_B @ sk_A)
% 0.79/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['46', '47'])).
% 0.79/1.01  thf('49', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('51', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.79/1.01      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.79/1.01  thf(d3_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.79/1.01  thf('52', plain,
% 0.79/1.01      (![X27 : $i, X28 : $i]:
% 0.79/1.01         (~ (v2_funct_2 @ X28 @ X27)
% 0.79/1.01          | ((k2_relat_1 @ X28) = (X27))
% 0.79/1.01          | ~ (v5_relat_1 @ X28 @ X27)
% 0.79/1.01          | ~ (v1_relat_1 @ X28))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.79/1.01  thf('53', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_B)
% 0.79/1.01        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.79/1.01        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['51', '52'])).
% 0.79/1.01  thf('54', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('55', plain,
% 0.79/1.01      (![X3 : $i, X4 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/1.01          | (v1_relat_1 @ X3)
% 0.79/1.01          | ~ (v1_relat_1 @ X4))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/1.01  thf('56', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['54', '55'])).
% 0.79/1.01  thf('57', plain,
% 0.79/1.01      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/1.01  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('59', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(cc2_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.79/1.01  thf('60', plain,
% 0.79/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.79/1.01         ((v5_relat_1 @ X17 @ X19)
% 0.79/1.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.01  thf('61', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.79/1.01      inference('sup-', [status(thm)], ['59', '60'])).
% 0.79/1.01  thf('62', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '58', '61'])).
% 0.79/1.01  thf('63', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X16)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.79/1.01          | ~ (v1_funct_1 @ X16)
% 0.79/1.01          | ~ (v1_relat_1 @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('64', plain,
% 0.79/1.01      (![X32 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.79/1.01  thf('65', plain,
% 0.79/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.79/1.01         ((v4_relat_1 @ X17 @ X18)
% 0.79/1.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.01  thf('66', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 0.79/1.01      inference('sup-', [status(thm)], ['64', '65'])).
% 0.79/1.01  thf('67', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.79/1.01           (k2_relat_1 @ X0))
% 0.79/1.01          | ~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0))),
% 0.79/1.01      inference('sup+', [status(thm)], ['63', '66'])).
% 0.79/1.01  thf('68', plain,
% 0.79/1.01      (((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['62', '67'])).
% 0.79/1.01  thf('69', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('70', plain,
% 0.79/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X24)
% 0.79/1.01          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.79/1.01          | (v2_funct_1 @ X24)
% 0.79/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.79/1.01  thf('71', plain,
% 0.79/1.01      (((v2_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['69', '70'])).
% 0.79/1.01  thf('72', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.79/1.01  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('77', plain,
% 0.79/1.01      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)),
% 0.79/1.01      inference('demod', [status(thm)], ['68', '74', '75', '76'])).
% 0.79/1.01  thf(t209_relat_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.79/1.01       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.79/1.01  thf('78', plain,
% 0.79/1.01      (![X10 : $i, X11 : $i]:
% 0.79/1.01         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.79/1.01          | ~ (v4_relat_1 @ X10 @ X11)
% 0.79/1.01          | ~ (v1_relat_1 @ X10))),
% 0.79/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.79/1.01  thf('79', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.79/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.79/1.01            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['77', '78'])).
% 0.79/1.01  thf('80', plain,
% 0.79/1.01      ((~ (v2_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.79/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.79/1.01            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['45', '79'])).
% 0.79/1.01  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.79/1.01  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('84', plain,
% 0.79/1.01      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.79/1.01         = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.79/1.01  thf('85', plain,
% 0.79/1.01      ((((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.79/1.01          = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['36', '84'])).
% 0.79/1.01  thf('86', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '58', '61'])).
% 0.79/1.01  thf('87', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 0.79/1.01      inference('sup-', [status(thm)], ['64', '65'])).
% 0.79/1.01  thf('88', plain,
% 0.79/1.01      (![X10 : $i, X11 : $i]:
% 0.79/1.01         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.79/1.01          | ~ (v4_relat_1 @ X10 @ X11)
% 0.79/1.01          | ~ (v1_relat_1 @ X10))),
% 0.79/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.79/1.01  thf('89', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.79/1.01          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['87', '88'])).
% 0.79/1.01  thf('90', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['42', '43'])).
% 0.79/1.01  thf('91', plain,
% 0.79/1.01      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['89', '90'])).
% 0.79/1.01  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('94', plain, ((v2_funct_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.79/1.01  thf('95', plain,
% 0.79/1.01      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['85', '86', '91', '92', '93', '94'])).
% 0.79/1.01  thf('96', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.79/1.01         = (k6_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['34', '35', '95'])).
% 0.79/1.01  thf('97', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.79/1.01  thf('98', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('split', [status(esa)], ['1'])).
% 0.79/1.01  thf('99', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('100', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01           (k6_relat_1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('demod', [status(thm)], ['98', '99'])).
% 0.79/1.01  thf('101', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01            sk_B) @ 
% 0.79/1.01           (k6_relat_1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['97', '100'])).
% 0.79/1.01  thf('102', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.79/1.01           (k6_relat_1 @ sk_A)))
% 0.79/1.01         <= (~
% 0.79/1.01             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['96', '101'])).
% 0.79/1.01  thf('103', plain,
% 0.79/1.01      (![X32 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.79/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.79/1.01  thf(reflexivity_r2_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.79/1.01  thf('104', plain,
% 0.79/1.01      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.79/1.01         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.79/1.01          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.79/1.01          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.79/1.01      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.79/1.01  thf('105', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.79/1.01      inference('condensation', [status(thm)], ['104'])).
% 0.79/1.01  thf('106', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['103', '105'])).
% 0.79/1.01  thf('107', plain,
% 0.79/1.01      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01         (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['102', '106'])).
% 0.79/1.01  thf('108', plain,
% 0.79/1.01      (~
% 0.79/1.01       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01         (k6_partfun1 @ sk_A))) | 
% 0.79/1.01       ~
% 0.79/1.01       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.79/1.01          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.79/1.01         (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('split', [status(esa)], ['1'])).
% 0.79/1.01  thf('109', plain,
% 0.79/1.01      (~
% 0.79/1.01       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.79/1.01         (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('sat_resolution*', [status(thm)], ['107', '108'])).
% 0.79/1.01  thf('110', plain,
% 0.79/1.01      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.79/1.01          (k6_relat_1 @ sk_A))),
% 0.79/1.01      inference('simpl_trail', [status(thm)], ['12', '109'])).
% 0.79/1.01  thf('111', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.79/1.01  thf('112', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('113', plain,
% 0.79/1.01      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.79/1.01          | ~ (v1_funct_1 @ X33)
% 0.79/1.01          | ~ (v1_funct_1 @ X36)
% 0.79/1.01          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.79/1.01          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 0.79/1.01              = (k5_relat_1 @ X33 @ X36)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/1.01  thf('114', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_B @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['112', '113'])).
% 0.79/1.01  thf('115', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('116', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_B @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['114', '115'])).
% 0.79/1.01  thf('117', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.79/1.01        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.79/1.01            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['111', '116'])).
% 0.79/1.01  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.79/1.01  thf('119', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.79/1.01         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['117', '118'])).
% 0.79/1.01  thf('120', plain,
% 0.79/1.01      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['110', '119'])).
% 0.79/1.01  thf('121', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.79/1.01           (k6_relat_1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['0', '120'])).
% 0.79/1.01  thf('122', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.79/1.01  thf('123', plain,
% 0.79/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.79/1.01         ((v4_relat_1 @ X17 @ X18)
% 0.79/1.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.01  thf('124', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.79/1.01      inference('sup-', [status(thm)], ['122', '123'])).
% 0.79/1.01  thf('125', plain,
% 0.79/1.01      (![X10 : $i, X11 : $i]:
% 0.79/1.01         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.79/1.01          | ~ (v4_relat_1 @ X10 @ X11)
% 0.79/1.01          | ~ (v1_relat_1 @ X10))),
% 0.79/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.79/1.01  thf('126', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.79/1.01        | ((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['124', '125'])).
% 0.79/1.01  thf('127', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.79/1.01  thf('128', plain,
% 0.79/1.01      (![X3 : $i, X4 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/1.01          | (v1_relat_1 @ X3)
% 0.79/1.01          | ~ (v1_relat_1 @ X4))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/1.01  thf('129', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.79/1.01        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['127', '128'])).
% 0.79/1.01  thf('130', plain,
% 0.79/1.01      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/1.01  thf('131', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['129', '130'])).
% 0.79/1.01  thf('132', plain,
% 0.79/1.01      (((k2_funct_1 @ sk_B) = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['126', '131'])).
% 0.79/1.01  thf(t148_relat_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( v1_relat_1 @ B ) =>
% 0.79/1.01       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.79/1.01  thf('133', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.79/1.01          | ~ (v1_relat_1 @ X7))),
% 0.79/1.01      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.79/1.01  thf('134', plain,
% 0.79/1.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_B))
% 0.79/1.01          = (k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['132', '133'])).
% 0.79/1.01  thf('135', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.79/1.01  thf('136', plain,
% 0.79/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X24)
% 0.79/1.01          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.79/1.01          | (v2_funct_2 @ X24 @ X26)
% 0.79/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.79/1.01  thf('137', plain,
% 0.79/1.01      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.79/1.01        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['135', '136'])).
% 0.79/1.01  thf('138', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('139', plain,
% 0.79/1.01      (![X29 : $i, X30 : $i]:
% 0.79/1.01         ((v3_funct_2 @ (k2_funct_2 @ X29 @ X30) @ X29 @ X29)
% 0.79/1.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.79/1.01          | ~ (v3_funct_2 @ X30 @ X29 @ X29)
% 0.79/1.01          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.79/1.01          | ~ (v1_funct_1 @ X30))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.79/1.01  thf('140', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.79/1.01        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['138', '139'])).
% 0.79/1.01  thf('141', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('142', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('143', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('144', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.79/1.01  thf('145', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.79/1.01      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 0.79/1.01  thf('146', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.79/1.01  thf('147', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.79/1.01      inference('demod', [status(thm)], ['137', '145', '146'])).
% 0.79/1.01  thf('148', plain,
% 0.79/1.01      (![X27 : $i, X28 : $i]:
% 0.79/1.01         (~ (v2_funct_2 @ X28 @ X27)
% 0.79/1.01          | ((k2_relat_1 @ X28) = (X27))
% 0.79/1.01          | ~ (v5_relat_1 @ X28 @ X27)
% 0.79/1.01          | ~ (v1_relat_1 @ X28))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.79/1.01  thf('149', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.79/1.01        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.79/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['147', '148'])).
% 0.79/1.01  thf('150', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['129', '130'])).
% 0.79/1.01  thf('151', plain,
% 0.79/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.79/1.01  thf('152', plain,
% 0.79/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.79/1.01         ((v5_relat_1 @ X17 @ X19)
% 0.79/1.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.01  thf('153', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.79/1.01      inference('sup-', [status(thm)], ['151', '152'])).
% 0.79/1.01  thf('154', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['149', '150', '153'])).
% 0.79/1.01  thf(d10_xboole_0, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/1.01  thf('155', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.79/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/1.01  thf('156', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/1.01      inference('simplify', [status(thm)], ['155'])).
% 0.79/1.01  thf('157', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '58', '61'])).
% 0.79/1.01  thf(t147_funct_1, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.01       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.79/1.01         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.79/1.01  thf('158', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i]:
% 0.79/1.01         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 0.79/1.01          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 0.79/1.01          | ~ (v1_funct_1 @ X13)
% 0.79/1.01          | ~ (v1_relat_1 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.79/1.01  thf('159', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (r1_tarski @ X0 @ sk_A)
% 0.79/1.01          | ~ (v1_relat_1 @ sk_B)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_B)
% 0.79/1.01          | ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)) = (X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['157', '158'])).
% 0.79/1.01  thf('160', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('161', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('162', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (r1_tarski @ X0 @ sk_A)
% 0.79/1.01          | ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)) = (X0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.79/1.01  thf('163', plain,
% 0.79/1.01      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['156', '162'])).
% 0.79/1.01  thf('164', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('165', plain,
% 0.79/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.79/1.01         ((v4_relat_1 @ X17 @ X18)
% 0.79/1.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.01  thf('166', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.79/1.01      inference('sup-', [status(thm)], ['164', '165'])).
% 0.79/1.01  thf('167', plain,
% 0.79/1.01      (![X10 : $i, X11 : $i]:
% 0.79/1.01         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.79/1.01          | ~ (v4_relat_1 @ X10 @ X11)
% 0.79/1.01          | ~ (v1_relat_1 @ X10))),
% 0.79/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.79/1.01  thf('168', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_B) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['166', '167'])).
% 0.79/1.01  thf('169', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('170', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['168', '169'])).
% 0.79/1.01  thf('171', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.79/1.01          | ~ (v1_relat_1 @ X7))),
% 0.79/1.01      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.79/1.01  thf(t169_relat_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v1_relat_1 @ A ) =>
% 0.79/1.01       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.79/1.01  thf('172', plain,
% 0.79/1.01      (![X9 : $i]:
% 0.79/1.01         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 0.79/1.01          | ~ (v1_relat_1 @ X9))),
% 0.79/1.01      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.79/1.01  thf('173', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.79/1.01            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.79/1.01          | ~ (v1_relat_1 @ X1)
% 0.79/1.01          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['171', '172'])).
% 0.79/1.01  thf('174', plain,
% 0.79/1.01      ((~ (v1_relat_1 @ sk_B)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.79/1.01        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.79/1.01            (k9_relat_1 @ sk_B @ sk_A))
% 0.79/1.01            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['170', '173'])).
% 0.79/1.01  thf('175', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('176', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('177', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['168', '169'])).
% 0.79/1.01  thf('178', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['168', '169'])).
% 0.79/1.01  thf('179', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.79/1.01          | ~ (v1_relat_1 @ X7))),
% 0.79/1.01      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.79/1.01  thf('180', plain,
% 0.79/1.01      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['178', '179'])).
% 0.79/1.01  thf('181', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('182', plain, (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['180', '181'])).
% 0.79/1.01  thf('183', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['168', '169'])).
% 0.79/1.01  thf('184', plain,
% 0.79/1.01      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['174', '175', '176', '177', '182', '183'])).
% 0.79/1.01  thf('185', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '58', '61'])).
% 0.79/1.01  thf('186', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['184', '185'])).
% 0.79/1.01  thf('187', plain, (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['163', '186'])).
% 0.79/1.01  thf('188', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/1.01      inference('simplify', [status(thm)], ['155'])).
% 0.79/1.01  thf(t177_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.79/1.01           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.79/1.01             ( B ) ) ) ) ))).
% 0.79/1.01  thf('189', plain,
% 0.79/1.01      (![X14 : $i, X15 : $i]:
% 0.79/1.01         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.79/1.01          | ((k9_relat_1 @ (k2_funct_1 @ X15) @ (k9_relat_1 @ X15 @ X14))
% 0.79/1.01              = (X14))
% 0.79/1.01          | ~ (v2_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_funct_1 @ X15)
% 0.79/1.01          | ~ (v1_relat_1 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.79/1.01  thf('190', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v2_funct_1 @ X0)
% 0.79/1.01          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.79/1.01              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['188', '189'])).
% 0.79/1.01  thf('191', plain,
% 0.79/1.01      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_B)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.79/1.01      inference('sup+', [status(thm)], ['187', '190'])).
% 0.79/1.01  thf('192', plain, ((v2_funct_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.79/1.01  thf('193', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('194', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('195', plain,
% 0.79/1.01      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 0.79/1.01  thf('196', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['129', '130'])).
% 0.79/1.01  thf('197', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['134', '154', '195', '196'])).
% 0.79/1.01  thf('198', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['103', '105'])).
% 0.79/1.01  thf('199', plain, ((v1_relat_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '57'])).
% 0.79/1.01  thf('200', plain, ((v1_funct_1 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('201', plain, ((v2_funct_1 @ sk_B)),
% 0.79/1.01      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.79/1.01  thf('202', plain, ($false),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['121', '197', '198', '199', '200', '201'])).
% 0.79/1.01  
% 0.79/1.01  % SZS output end Refutation
% 0.79/1.01  
% 0.79/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
