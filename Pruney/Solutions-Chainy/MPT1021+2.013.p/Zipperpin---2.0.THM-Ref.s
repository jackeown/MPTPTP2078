%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nAva55d7jP

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:12 EST 2020

% Result     : Theorem 22.28s
% Output     : Refutation 22.28s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 412 expanded)
%              Number of leaves         :   46 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          : 1348 (8846 expanded)
%              Number of equality atoms :   55 (  85 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( ( k2_funct_2 @ X48 @ X47 )
        = ( k2_funct_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) )
      | ~ ( v3_funct_2 @ X47 @ X48 @ X48 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X48 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('11',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8','9','10','11'])).

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
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

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

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('39',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_2 @ X36 @ X35 )
      | ( ( k2_relat_1 @ X36 )
        = X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('52',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('53',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('54',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','58'])).

thf('60',plain,
    ( ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('65',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('71',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','68','69','70'])).

thf('72',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','36','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('74',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('84',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','86'])).

thf('88',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('89',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('95',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('96',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['97'])).

thf('99',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('101',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('102',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['90','99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['87','103','104','105','106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nAva55d7jP
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:42:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 22.28/22.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 22.28/22.53  % Solved by: fo/fo7.sh
% 22.28/22.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.28/22.53  % done 8874 iterations in 22.075s
% 22.28/22.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 22.28/22.53  % SZS output start Refutation
% 22.28/22.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 22.28/22.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 22.28/22.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 22.28/22.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 22.28/22.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 22.28/22.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.28/22.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 22.28/22.53  thf(sk_B_type, type, sk_B: $i).
% 22.28/22.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 22.28/22.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 22.28/22.53  thf(sk_A_type, type, sk_A: $i).
% 22.28/22.53  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 22.28/22.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 22.28/22.53  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 22.28/22.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 22.28/22.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 22.28/22.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 22.28/22.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 22.28/22.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 22.28/22.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 22.28/22.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 22.28/22.53  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 22.28/22.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 22.28/22.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.28/22.53  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 22.28/22.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 22.28/22.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 22.28/22.53  thf(t61_funct_1, axiom,
% 22.28/22.53    (![A:$i]:
% 22.28/22.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 22.28/22.53       ( ( v2_funct_1 @ A ) =>
% 22.28/22.53         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 22.28/22.53             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 22.28/22.53           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 22.28/22.53             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 22.28/22.53  thf('0', plain,
% 22.28/22.53      (![X10 : $i]:
% 22.28/22.53         (~ (v2_funct_1 @ X10)
% 22.28/22.53          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 22.28/22.53              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 22.28/22.53          | ~ (v1_funct_1 @ X10)
% 22.28/22.53          | ~ (v1_relat_1 @ X10))),
% 22.28/22.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 22.28/22.53  thf(t88_funct_2, conjecture,
% 22.28/22.53    (![A:$i,B:$i]:
% 22.28/22.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 22.28/22.53         ( v3_funct_2 @ B @ A @ A ) & 
% 22.28/22.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 22.28/22.53       ( ( r2_relset_1 @
% 22.28/22.53           A @ A @ 
% 22.28/22.53           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 22.28/22.53           ( k6_partfun1 @ A ) ) & 
% 22.28/22.53         ( r2_relset_1 @
% 22.28/22.53           A @ A @ 
% 22.28/22.53           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 22.28/22.53           ( k6_partfun1 @ A ) ) ) ))).
% 22.28/22.53  thf(zf_stmt_0, negated_conjecture,
% 22.28/22.53    (~( ![A:$i,B:$i]:
% 22.28/22.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 22.28/22.53            ( v3_funct_2 @ B @ A @ A ) & 
% 22.28/22.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 22.28/22.53          ( ( r2_relset_1 @
% 22.28/22.53              A @ A @ 
% 22.28/22.53              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 22.28/22.53              ( k6_partfun1 @ A ) ) & 
% 22.28/22.53            ( r2_relset_1 @
% 22.28/22.53              A @ A @ 
% 22.28/22.53              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 22.28/22.53              ( k6_partfun1 @ A ) ) ) ) )),
% 22.28/22.53    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 22.28/22.53  thf('1', plain,
% 22.28/22.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.53           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 22.28/22.53            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 22.28/22.53           (k6_partfun1 @ sk_A))
% 22.28/22.53        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.53             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 22.28/22.53              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 22.28/22.53             (k6_partfun1 @ sk_A)))),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('2', plain,
% 22.28/22.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf(redefinition_k2_funct_2, axiom,
% 22.28/22.53    (![A:$i,B:$i]:
% 22.28/22.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 22.28/22.53         ( v3_funct_2 @ B @ A @ A ) & 
% 22.28/22.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 22.28/22.53       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 22.28/22.53  thf('3', plain,
% 22.28/22.53      (![X47 : $i, X48 : $i]:
% 22.28/22.53         (((k2_funct_2 @ X48 @ X47) = (k2_funct_1 @ X47))
% 22.28/22.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))
% 22.28/22.53          | ~ (v3_funct_2 @ X47 @ X48 @ X48)
% 22.28/22.53          | ~ (v1_funct_2 @ X47 @ X48 @ X48)
% 22.28/22.53          | ~ (v1_funct_1 @ X47))),
% 22.28/22.53      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 22.28/22.53  thf('4', plain,
% 22.28/22.53      ((~ (v1_funct_1 @ sk_B)
% 22.28/22.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.53        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 22.28/22.53      inference('sup-', [status(thm)], ['2', '3'])).
% 22.28/22.53  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 22.28/22.53      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 22.28/22.53  thf(redefinition_k6_partfun1, axiom,
% 22.28/22.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 22.28/22.53  thf('9', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 22.28/22.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.28/22.53  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 22.28/22.53      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 22.28/22.53  thf('11', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 22.28/22.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.28/22.53  thf('12', plain,
% 22.28/22.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.53           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 22.28/22.53            (k2_funct_1 @ sk_B)) @ 
% 22.28/22.53           (k6_relat_1 @ sk_A))
% 22.28/22.53        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.53             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 22.28/22.53              sk_B) @ 
% 22.28/22.53             (k6_relat_1 @ sk_A)))),
% 22.28/22.53      inference('demod', [status(thm)], ['1', '8', '9', '10', '11'])).
% 22.28/22.53  thf('13', plain,
% 22.28/22.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('14', plain,
% 22.28/22.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf(dt_k2_funct_2, axiom,
% 22.28/22.53    (![A:$i,B:$i]:
% 22.28/22.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 22.28/22.53         ( v3_funct_2 @ B @ A @ A ) & 
% 22.28/22.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 22.28/22.53       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 22.28/22.53         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 22.28/22.53         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 22.28/22.53         ( m1_subset_1 @
% 22.28/22.53           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 22.28/22.53  thf('15', plain,
% 22.28/22.53      (![X37 : $i, X38 : $i]:
% 22.28/22.53         ((m1_subset_1 @ (k2_funct_2 @ X37 @ X38) @ 
% 22.28/22.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 22.28/22.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 22.28/22.53          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 22.28/22.53          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 22.28/22.53          | ~ (v1_funct_1 @ X38))),
% 22.28/22.53      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 22.28/22.53  thf('16', plain,
% 22.28/22.53      ((~ (v1_funct_1 @ sk_B)
% 22.28/22.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.53        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 22.28/22.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 22.28/22.53      inference('sup-', [status(thm)], ['14', '15'])).
% 22.28/22.53  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.53  thf('20', plain,
% 22.28/22.53      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 22.28/22.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.53      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 22.28/22.53  thf(redefinition_k1_partfun1, axiom,
% 22.28/22.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 22.28/22.53     ( ( ( v1_funct_1 @ E ) & 
% 22.28/22.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 22.28/22.53         ( v1_funct_1 @ F ) & 
% 22.28/22.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 22.28/22.53       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 22.28/22.53  thf('21', plain,
% 22.28/22.53      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 22.28/22.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 22.28/22.53          | ~ (v1_funct_1 @ X41)
% 22.28/22.53          | ~ (v1_funct_1 @ X44)
% 22.28/22.53          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 22.28/22.53          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 22.28/22.53              = (k5_relat_1 @ X41 @ X44)))),
% 22.28/22.53      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 22.28/22.53  thf('22', plain,
% 22.28/22.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.53         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 22.28/22.54            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 22.28/22.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.28/22.54          | ~ (v1_funct_1 @ X0)
% 22.28/22.54          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 22.28/22.54      inference('sup-', [status(thm)], ['20', '21'])).
% 22.28/22.54  thf('23', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('24', plain,
% 22.28/22.54      (![X37 : $i, X38 : $i]:
% 22.28/22.54         ((v1_funct_1 @ (k2_funct_2 @ X37 @ X38))
% 22.28/22.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 22.28/22.54          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 22.28/22.54          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 22.28/22.54          | ~ (v1_funct_1 @ X38))),
% 22.28/22.54      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 22.28/22.54  thf('25', plain,
% 22.28/22.54      ((~ (v1_funct_1 @ sk_B)
% 22.28/22.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.54        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 22.28/22.54      inference('sup-', [status(thm)], ['23', '24'])).
% 22.28/22.54  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 22.28/22.54  thf('30', plain,
% 22.28/22.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 22.28/22.54            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 22.28/22.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.28/22.54          | ~ (v1_funct_1 @ X0))),
% 22.28/22.54      inference('demod', [status(thm)], ['22', '29'])).
% 22.28/22.54  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 22.28/22.54  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 22.28/22.54  thf('33', plain,
% 22.28/22.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 22.28/22.54            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 22.28/22.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.28/22.54          | ~ (v1_funct_1 @ X0))),
% 22.28/22.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 22.28/22.54  thf('34', plain,
% 22.28/22.54      ((~ (v1_funct_1 @ sk_B)
% 22.28/22.54        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 22.28/22.54            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 22.28/22.54      inference('sup-', [status(thm)], ['13', '33'])).
% 22.28/22.54  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('36', plain,
% 22.28/22.54      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 22.28/22.54         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['34', '35'])).
% 22.28/22.54  thf('37', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf(cc2_funct_2, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i]:
% 22.28/22.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.28/22.54       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 22.28/22.54         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 22.28/22.54  thf('38', plain,
% 22.28/22.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 22.28/22.54         (~ (v1_funct_1 @ X24)
% 22.28/22.54          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 22.28/22.54          | (v2_funct_2 @ X24 @ X26)
% 22.28/22.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 22.28/22.54      inference('cnf', [status(esa)], [cc2_funct_2])).
% 22.28/22.54  thf('39', plain,
% 22.28/22.54      (((v2_funct_2 @ sk_B @ sk_A)
% 22.28/22.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.54        | ~ (v1_funct_1 @ sk_B))),
% 22.28/22.54      inference('sup-', [status(thm)], ['37', '38'])).
% 22.28/22.54  thf('40', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('42', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 22.28/22.54      inference('demod', [status(thm)], ['39', '40', '41'])).
% 22.28/22.54  thf(d3_funct_2, axiom,
% 22.28/22.54    (![A:$i,B:$i]:
% 22.28/22.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 22.28/22.54       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 22.28/22.54  thf('43', plain,
% 22.28/22.54      (![X35 : $i, X36 : $i]:
% 22.28/22.54         (~ (v2_funct_2 @ X36 @ X35)
% 22.28/22.54          | ((k2_relat_1 @ X36) = (X35))
% 22.28/22.54          | ~ (v5_relat_1 @ X36 @ X35)
% 22.28/22.54          | ~ (v1_relat_1 @ X36))),
% 22.28/22.54      inference('cnf', [status(esa)], [d3_funct_2])).
% 22.28/22.54  thf('44', plain,
% 22.28/22.54      ((~ (v1_relat_1 @ sk_B)
% 22.28/22.54        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 22.28/22.54        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 22.28/22.54      inference('sup-', [status(thm)], ['42', '43'])).
% 22.28/22.54  thf('45', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf(cc1_relset_1, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i]:
% 22.28/22.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.28/22.54       ( v1_relat_1 @ C ) ))).
% 22.28/22.54  thf('46', plain,
% 22.28/22.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 22.28/22.54         ((v1_relat_1 @ X11)
% 22.28/22.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 22.28/22.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 22.28/22.54  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 22.28/22.54      inference('sup-', [status(thm)], ['45', '46'])).
% 22.28/22.54  thf('48', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf(cc2_relset_1, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i]:
% 22.28/22.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.28/22.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 22.28/22.54  thf('49', plain,
% 22.28/22.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 22.28/22.54         ((v5_relat_1 @ X14 @ X16)
% 22.28/22.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 22.28/22.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 22.28/22.54  thf('50', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 22.28/22.54      inference('sup-', [status(thm)], ['48', '49'])).
% 22.28/22.54  thf('51', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 22.28/22.54      inference('demod', [status(thm)], ['44', '47', '50'])).
% 22.28/22.54  thf('52', plain,
% 22.28/22.54      (![X10 : $i]:
% 22.28/22.54         (~ (v2_funct_1 @ X10)
% 22.28/22.54          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 22.28/22.54              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 22.28/22.54          | ~ (v1_funct_1 @ X10)
% 22.28/22.54          | ~ (v1_relat_1 @ X10))),
% 22.28/22.54      inference('cnf', [status(esa)], [t61_funct_1])).
% 22.28/22.54  thf(dt_k6_partfun1, axiom,
% 22.28/22.54    (![A:$i]:
% 22.28/22.54     ( ( m1_subset_1 @
% 22.28/22.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 22.28/22.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 22.28/22.54  thf('53', plain,
% 22.28/22.54      (![X40 : $i]:
% 22.28/22.54         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 22.28/22.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 22.28/22.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 22.28/22.54  thf('54', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 22.28/22.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.28/22.54  thf('55', plain,
% 22.28/22.54      (![X40 : $i]:
% 22.28/22.54         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 22.28/22.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 22.28/22.54      inference('demod', [status(thm)], ['53', '54'])).
% 22.28/22.54  thf(reflexivity_r2_relset_1, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i,D:$i]:
% 22.28/22.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 22.28/22.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.28/22.54       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 22.28/22.54  thf('56', plain,
% 22.28/22.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 22.28/22.54         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 22.28/22.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 22.28/22.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 22.28/22.54      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 22.28/22.54  thf('57', plain,
% 22.28/22.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.54         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 22.28/22.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 22.28/22.54      inference('condensation', [status(thm)], ['56'])).
% 22.28/22.54  thf('58', plain,
% 22.28/22.54      (![X0 : $i]:
% 22.28/22.54         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 22.28/22.54      inference('sup-', [status(thm)], ['55', '57'])).
% 22.28/22.54  thf('59', plain,
% 22.28/22.54      (![X0 : $i]:
% 22.28/22.54         ((r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 22.28/22.54           (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 22.28/22.54           (k6_relat_1 @ (k2_relat_1 @ X0)))
% 22.28/22.54          | ~ (v1_relat_1 @ X0)
% 22.28/22.54          | ~ (v1_funct_1 @ X0)
% 22.28/22.54          | ~ (v2_funct_1 @ X0))),
% 22.28/22.54      inference('sup+', [status(thm)], ['52', '58'])).
% 22.28/22.54  thf('60', plain,
% 22.28/22.54      (((r2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ 
% 22.28/22.54         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 22.28/22.54         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 22.28/22.54        | ~ (v2_funct_1 @ sk_B)
% 22.28/22.54        | ~ (v1_funct_1 @ sk_B)
% 22.28/22.54        | ~ (v1_relat_1 @ sk_B))),
% 22.28/22.54      inference('sup+', [status(thm)], ['51', '59'])).
% 22.28/22.54  thf('61', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 22.28/22.54      inference('demod', [status(thm)], ['44', '47', '50'])).
% 22.28/22.54  thf('62', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 22.28/22.54      inference('demod', [status(thm)], ['44', '47', '50'])).
% 22.28/22.54  thf('63', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('64', plain,
% 22.28/22.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 22.28/22.54         (~ (v1_funct_1 @ X24)
% 22.28/22.54          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 22.28/22.54          | (v2_funct_1 @ X24)
% 22.28/22.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 22.28/22.54      inference('cnf', [status(esa)], [cc2_funct_2])).
% 22.28/22.54  thf('65', plain,
% 22.28/22.54      (((v2_funct_1 @ sk_B)
% 22.28/22.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 22.28/22.54        | ~ (v1_funct_1 @ sk_B))),
% 22.28/22.54      inference('sup-', [status(thm)], ['63', '64'])).
% 22.28/22.54  thf('66', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('68', plain, ((v2_funct_1 @ sk_B)),
% 22.28/22.54      inference('demod', [status(thm)], ['65', '66', '67'])).
% 22.28/22.54  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 22.28/22.54      inference('sup-', [status(thm)], ['45', '46'])).
% 22.28/22.54  thf('71', plain,
% 22.28/22.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.54        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A))),
% 22.28/22.54      inference('demod', [status(thm)], ['60', '61', '62', '68', '69', '70'])).
% 22.28/22.54  thf('72', plain,
% 22.28/22.54      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.54          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 22.28/22.54          (k6_relat_1 @ sk_A))),
% 22.28/22.54      inference('demod', [status(thm)], ['12', '36', '71'])).
% 22.28/22.54  thf('73', plain,
% 22.28/22.54      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 22.28/22.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 22.28/22.54  thf('74', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 22.28/22.54  thf('75', plain,
% 22.28/22.54      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 22.28/22.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('demod', [status(thm)], ['73', '74'])).
% 22.28/22.54  thf('76', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('77', plain,
% 22.28/22.54      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 22.28/22.54         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 22.28/22.54          | ~ (v1_funct_1 @ X41)
% 22.28/22.54          | ~ (v1_funct_1 @ X44)
% 22.28/22.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 22.28/22.54          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 22.28/22.54              = (k5_relat_1 @ X41 @ X44)))),
% 22.28/22.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 22.28/22.54  thf('78', plain,
% 22.28/22.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 22.28/22.54            = (k5_relat_1 @ sk_B @ X0))
% 22.28/22.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.28/22.54          | ~ (v1_funct_1 @ X0)
% 22.28/22.54          | ~ (v1_funct_1 @ sk_B))),
% 22.28/22.54      inference('sup-', [status(thm)], ['76', '77'])).
% 22.28/22.54  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('80', plain,
% 22.28/22.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 22.28/22.54            = (k5_relat_1 @ sk_B @ X0))
% 22.28/22.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.28/22.54          | ~ (v1_funct_1 @ X0))),
% 22.28/22.54      inference('demod', [status(thm)], ['78', '79'])).
% 22.28/22.54  thf('81', plain,
% 22.28/22.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 22.28/22.54        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 22.28/22.54            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 22.28/22.54      inference('sup-', [status(thm)], ['75', '80'])).
% 22.28/22.54  thf('82', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 22.28/22.54  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 22.28/22.54  thf('84', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['82', '83'])).
% 22.28/22.54  thf('85', plain,
% 22.28/22.54      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 22.28/22.54         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 22.28/22.54      inference('demod', [status(thm)], ['81', '84'])).
% 22.28/22.54  thf('86', plain,
% 22.28/22.54      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 22.28/22.54          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 22.28/22.54      inference('demod', [status(thm)], ['72', '85'])).
% 22.28/22.54  thf('87', plain,
% 22.28/22.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 22.28/22.54           (k6_relat_1 @ sk_A))
% 22.28/22.54        | ~ (v1_relat_1 @ sk_B)
% 22.28/22.54        | ~ (v1_funct_1 @ sk_B)
% 22.28/22.54        | ~ (v2_funct_1 @ sk_B))),
% 22.28/22.54      inference('sup-', [status(thm)], ['0', '86'])).
% 22.28/22.54  thf('88', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf(d1_funct_2, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i]:
% 22.28/22.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.28/22.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 22.28/22.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 22.28/22.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 22.28/22.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 22.28/22.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 22.28/22.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 22.28/22.54  thf(zf_stmt_1, axiom,
% 22.28/22.54    (![C:$i,B:$i,A:$i]:
% 22.28/22.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 22.28/22.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 22.28/22.54  thf('89', plain,
% 22.28/22.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 22.28/22.54         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 22.28/22.54          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 22.28/22.54          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 22.28/22.54  thf('90', plain,
% 22.28/22.54      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 22.28/22.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 22.28/22.54      inference('sup-', [status(thm)], ['88', '89'])).
% 22.28/22.54  thf('91', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 22.28/22.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 22.28/22.54  thf(zf_stmt_4, axiom,
% 22.28/22.54    (![B:$i,A:$i]:
% 22.28/22.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 22.28/22.54       ( zip_tseitin_0 @ B @ A ) ))).
% 22.28/22.54  thf(zf_stmt_5, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i]:
% 22.28/22.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.28/22.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 22.28/22.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 22.28/22.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 22.28/22.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 22.28/22.54  thf('92', plain,
% 22.28/22.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 22.28/22.54         (~ (zip_tseitin_0 @ X32 @ X33)
% 22.28/22.54          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 22.28/22.54          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 22.28/22.54  thf('93', plain,
% 22.28/22.54      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 22.28/22.54      inference('sup-', [status(thm)], ['91', '92'])).
% 22.28/22.54  thf('94', plain,
% 22.28/22.54      (![X27 : $i, X28 : $i]:
% 22.28/22.54         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 22.28/22.54  thf('95', plain,
% 22.28/22.54      (![X27 : $i, X28 : $i]:
% 22.28/22.54         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 22.28/22.54  thf('96', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 22.28/22.54      inference('simplify', [status(thm)], ['95'])).
% 22.28/22.54  thf('97', plain,
% 22.28/22.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.28/22.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 22.28/22.54      inference('sup+', [status(thm)], ['94', '96'])).
% 22.28/22.54  thf('98', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 22.28/22.54      inference('eq_fact', [status(thm)], ['97'])).
% 22.28/22.54  thf('99', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 22.28/22.54      inference('demod', [status(thm)], ['93', '98'])).
% 22.28/22.54  thf('100', plain,
% 22.28/22.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf(redefinition_k1_relset_1, axiom,
% 22.28/22.54    (![A:$i,B:$i,C:$i]:
% 22.28/22.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.28/22.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 22.28/22.54  thf('101', plain,
% 22.28/22.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 22.28/22.54         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 22.28/22.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 22.28/22.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 22.28/22.54  thf('102', plain,
% 22.28/22.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 22.28/22.54      inference('sup-', [status(thm)], ['100', '101'])).
% 22.28/22.54  thf('103', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 22.28/22.54      inference('demod', [status(thm)], ['90', '99', '102'])).
% 22.28/22.54  thf('104', plain,
% 22.28/22.54      (![X0 : $i]:
% 22.28/22.54         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 22.28/22.54      inference('sup-', [status(thm)], ['55', '57'])).
% 22.28/22.54  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 22.28/22.54      inference('sup-', [status(thm)], ['45', '46'])).
% 22.28/22.54  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 22.28/22.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.28/22.54  thf('107', plain, ((v2_funct_1 @ sk_B)),
% 22.28/22.54      inference('demod', [status(thm)], ['65', '66', '67'])).
% 22.28/22.54  thf('108', plain, ($false),
% 22.28/22.54      inference('demod', [status(thm)],
% 22.28/22.54                ['87', '103', '104', '105', '106', '107'])).
% 22.28/22.54  
% 22.28/22.54  % SZS output end Refutation
% 22.28/22.54  
% 22.41/22.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
