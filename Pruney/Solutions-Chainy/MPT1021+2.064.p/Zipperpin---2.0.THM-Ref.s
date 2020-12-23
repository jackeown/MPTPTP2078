%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iFE6p64bWa

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:21 EST 2020

% Result     : Theorem 47.27s
% Output     : Refutation 47.27s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 583 expanded)
%              Number of leaves         :   47 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          : 1781 (11836 expanded)
%              Number of equality atoms :   71 ( 147 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
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

thf('33',plain,(
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

thf('34',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ X13 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_2 @ X36 @ X35 )
      | ( ( k2_relat_1 @ X36 )
        = X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X13 ) @ X13 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('54',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('73',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('74',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
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
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','76','77','78','79'])).

thf('81',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','80'])).

thf('82',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('83',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('87',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('92',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
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
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('101',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('104',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
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

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('108',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('111',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('113',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('114',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['112','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['115'])).

thf('117',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['111','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('119',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('120',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','117','120'])).

thf('122',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('123',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['121','124'])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','117','120'])).

thf('127',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('128',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('130',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('132',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','132'])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','117','120'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('136',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('137',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('139',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138'])).

thf('140',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['99','102','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['90','140','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iFE6p64bWa
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:18:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 47.27/47.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.27/47.54  % Solved by: fo/fo7.sh
% 47.27/47.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.27/47.54  % done 6006 iterations in 47.091s
% 47.27/47.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.27/47.54  % SZS output start Refutation
% 47.27/47.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 47.27/47.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 47.27/47.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 47.27/47.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 47.27/47.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 47.27/47.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 47.27/47.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 47.27/47.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 47.27/47.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 47.27/47.54  thf(sk_B_type, type, sk_B: $i).
% 47.27/47.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 47.27/47.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 47.27/47.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 47.27/47.54  thf(sk_A_type, type, sk_A: $i).
% 47.27/47.54  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 47.27/47.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 47.27/47.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 47.27/47.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 47.27/47.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 47.27/47.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.27/47.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 47.27/47.54  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 47.27/47.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 47.27/47.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 47.27/47.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 47.27/47.54  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 47.27/47.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 47.27/47.54  thf(t88_funct_2, conjecture,
% 47.27/47.54    (![A:$i,B:$i]:
% 47.27/47.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 47.27/47.54         ( v3_funct_2 @ B @ A @ A ) & 
% 47.27/47.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.27/47.54       ( ( r2_relset_1 @
% 47.27/47.54           A @ A @ 
% 47.27/47.54           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 47.27/47.54           ( k6_partfun1 @ A ) ) & 
% 47.27/47.54         ( r2_relset_1 @
% 47.27/47.54           A @ A @ 
% 47.27/47.54           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 47.27/47.54           ( k6_partfun1 @ A ) ) ) ))).
% 47.27/47.54  thf(zf_stmt_0, negated_conjecture,
% 47.27/47.54    (~( ![A:$i,B:$i]:
% 47.27/47.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 47.27/47.54            ( v3_funct_2 @ B @ A @ A ) & 
% 47.27/47.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.27/47.54          ( ( r2_relset_1 @
% 47.27/47.54              A @ A @ 
% 47.27/47.54              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 47.27/47.54              ( k6_partfun1 @ A ) ) & 
% 47.27/47.54            ( r2_relset_1 @
% 47.27/47.54              A @ A @ 
% 47.27/47.54              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 47.27/47.54              ( k6_partfun1 @ A ) ) ) ) )),
% 47.27/47.54    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 47.27/47.54  thf('0', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 47.27/47.54           (k6_partfun1 @ sk_A))
% 47.27/47.54        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54             (k6_partfun1 @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('1', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 47.27/47.54           (k6_partfun1 @ sk_A)))
% 47.27/47.54         <= (~
% 47.27/47.54             ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 47.27/47.54               (k6_partfun1 @ sk_A))))),
% 47.27/47.54      inference('split', [status(esa)], ['0'])).
% 47.27/47.54  thf('2', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(redefinition_k2_funct_2, axiom,
% 47.27/47.54    (![A:$i,B:$i]:
% 47.27/47.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 47.27/47.54         ( v3_funct_2 @ B @ A @ A ) & 
% 47.27/47.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.27/47.54       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 47.27/47.54  thf('3', plain,
% 47.27/47.54      (![X47 : $i, X48 : $i]:
% 47.27/47.54         (((k2_funct_2 @ X48 @ X47) = (k2_funct_1 @ X47))
% 47.27/47.54          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))
% 47.27/47.54          | ~ (v3_funct_2 @ X47 @ X48 @ X48)
% 47.27/47.54          | ~ (v1_funct_2 @ X47 @ X48 @ X48)
% 47.27/47.54          | ~ (v1_funct_1 @ X47))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 47.27/47.54  thf('4', plain,
% 47.27/47.54      ((~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['2', '3'])).
% 47.27/47.54  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 47.27/47.54  thf('9', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54            (k2_funct_1 @ sk_B)) @ 
% 47.27/47.54           (k6_partfun1 @ sk_A)))
% 47.27/47.54         <= (~
% 47.27/47.54             ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 47.27/47.54               (k6_partfun1 @ sk_A))))),
% 47.27/47.54      inference('demod', [status(thm)], ['1', '8'])).
% 47.27/47.54  thf('10', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('11', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(dt_k2_funct_2, axiom,
% 47.27/47.54    (![A:$i,B:$i]:
% 47.27/47.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 47.27/47.54         ( v3_funct_2 @ B @ A @ A ) & 
% 47.27/47.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 47.27/47.54       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 47.27/47.54         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 47.27/47.54         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 47.27/47.54         ( m1_subset_1 @
% 47.27/47.54           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 47.27/47.54  thf('12', plain,
% 47.27/47.54      (![X37 : $i, X38 : $i]:
% 47.27/47.54         ((m1_subset_1 @ (k2_funct_2 @ X37 @ X38) @ 
% 47.27/47.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 47.27/47.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 47.27/47.54          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 47.27/47.54          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 47.27/47.54          | ~ (v1_funct_1 @ X38))),
% 47.27/47.54      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 47.27/47.54  thf('13', plain,
% 47.27/47.54      ((~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 47.27/47.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['11', '12'])).
% 47.27/47.54  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('17', plain,
% 47.27/47.54      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 47.27/47.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 47.27/47.54  thf(redefinition_k1_partfun1, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 47.27/47.54     ( ( ( v1_funct_1 @ E ) & 
% 47.27/47.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 47.27/47.54         ( v1_funct_1 @ F ) & 
% 47.27/47.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 47.27/47.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 47.27/47.54  thf('18', plain,
% 47.27/47.54      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 47.27/47.54         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 47.27/47.54          | ~ (v1_funct_1 @ X41)
% 47.27/47.54          | ~ (v1_funct_1 @ X44)
% 47.27/47.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 47.27/47.54          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 47.27/47.54              = (k5_relat_1 @ X41 @ X44)))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 47.27/47.54  thf('19', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.27/47.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 47.27/47.54            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 47.27/47.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.27/47.54          | ~ (v1_funct_1 @ X0)
% 47.27/47.54          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['17', '18'])).
% 47.27/47.54  thf('20', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('21', plain,
% 47.27/47.54      (![X37 : $i, X38 : $i]:
% 47.27/47.54         ((v1_funct_1 @ (k2_funct_2 @ X37 @ X38))
% 47.27/47.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 47.27/47.54          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 47.27/47.54          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 47.27/47.54          | ~ (v1_funct_1 @ X38))),
% 47.27/47.54      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 47.27/47.54  thf('22', plain,
% 47.27/47.54      ((~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['20', '21'])).
% 47.27/47.54  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('24', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('26', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 47.27/47.54  thf('27', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.27/47.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 47.27/47.54            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 47.27/47.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.27/47.54          | ~ (v1_funct_1 @ X0))),
% 47.27/47.54      inference('demod', [status(thm)], ['19', '26'])).
% 47.27/47.54  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 47.27/47.54  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 47.27/47.54  thf('30', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.27/47.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 47.27/47.54            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 47.27/47.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.27/47.54          | ~ (v1_funct_1 @ X0))),
% 47.27/47.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 47.27/47.54  thf('31', plain,
% 47.27/47.54      ((~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 47.27/47.54            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['10', '30'])).
% 47.27/47.54  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(t61_funct_1, axiom,
% 47.27/47.54    (![A:$i]:
% 47.27/47.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 47.27/47.54       ( ( v2_funct_1 @ A ) =>
% 47.27/47.54         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 47.27/47.54             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 47.27/47.54           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 47.27/47.54             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 47.27/47.54  thf('33', plain,
% 47.27/47.54      (![X13 : $i]:
% 47.27/47.54         (~ (v2_funct_1 @ X13)
% 47.27/47.54          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 47.27/47.54              = (k6_relat_1 @ (k2_relat_1 @ X13)))
% 47.27/47.54          | ~ (v1_funct_1 @ X13)
% 47.27/47.54          | ~ (v1_relat_1 @ X13))),
% 47.27/47.54      inference('cnf', [status(esa)], [t61_funct_1])).
% 47.27/47.54  thf(redefinition_k6_partfun1, axiom,
% 47.27/47.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 47.27/47.54  thf('34', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 47.27/47.54  thf('35', plain,
% 47.27/47.54      (![X13 : $i]:
% 47.27/47.54         (~ (v2_funct_1 @ X13)
% 47.27/47.54          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 47.27/47.54              = (k6_partfun1 @ (k2_relat_1 @ X13)))
% 47.27/47.54          | ~ (v1_funct_1 @ X13)
% 47.27/47.54          | ~ (v1_relat_1 @ X13))),
% 47.27/47.54      inference('demod', [status(thm)], ['33', '34'])).
% 47.27/47.54  thf('36', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(cc2_funct_2, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i]:
% 47.27/47.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.27/47.54       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 47.27/47.54         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 47.27/47.54  thf('37', plain,
% 47.27/47.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 47.27/47.54         (~ (v1_funct_1 @ X24)
% 47.27/47.54          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 47.27/47.54          | (v2_funct_2 @ X24 @ X26)
% 47.27/47.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 47.27/47.54      inference('cnf', [status(esa)], [cc2_funct_2])).
% 47.27/47.54  thf('38', plain,
% 47.27/47.54      (((v2_funct_2 @ sk_B @ sk_A)
% 47.27/47.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ~ (v1_funct_1 @ sk_B))),
% 47.27/47.54      inference('sup-', [status(thm)], ['36', '37'])).
% 47.27/47.54  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 47.27/47.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 47.27/47.54  thf(d3_funct_2, axiom,
% 47.27/47.54    (![A:$i,B:$i]:
% 47.27/47.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 47.27/47.54       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 47.27/47.54  thf('42', plain,
% 47.27/47.54      (![X35 : $i, X36 : $i]:
% 47.27/47.54         (~ (v2_funct_2 @ X36 @ X35)
% 47.27/47.54          | ((k2_relat_1 @ X36) = (X35))
% 47.27/47.54          | ~ (v5_relat_1 @ X36 @ X35)
% 47.27/47.54          | ~ (v1_relat_1 @ X36))),
% 47.27/47.54      inference('cnf', [status(esa)], [d3_funct_2])).
% 47.27/47.54  thf('43', plain,
% 47.27/47.54      ((~ (v1_relat_1 @ sk_B)
% 47.27/47.54        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 47.27/47.54        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['41', '42'])).
% 47.27/47.54  thf('44', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(cc2_relat_1, axiom,
% 47.27/47.54    (![A:$i]:
% 47.27/47.54     ( ( v1_relat_1 @ A ) =>
% 47.27/47.54       ( ![B:$i]:
% 47.27/47.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 47.27/47.54  thf('45', plain,
% 47.27/47.54      (![X4 : $i, X5 : $i]:
% 47.27/47.54         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 47.27/47.54          | (v1_relat_1 @ X4)
% 47.27/47.54          | ~ (v1_relat_1 @ X5))),
% 47.27/47.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 47.27/47.54  thf('46', plain,
% 47.27/47.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 47.27/47.54      inference('sup-', [status(thm)], ['44', '45'])).
% 47.27/47.54  thf(fc6_relat_1, axiom,
% 47.27/47.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 47.27/47.54  thf('47', plain,
% 47.27/47.54      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 47.27/47.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 47.27/47.54  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['46', '47'])).
% 47.27/47.54  thf('49', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(cc2_relset_1, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i]:
% 47.27/47.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.27/47.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 47.27/47.54  thf('50', plain,
% 47.27/47.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 47.27/47.54         ((v5_relat_1 @ X14 @ X16)
% 47.27/47.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 47.27/47.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 47.27/47.54  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 47.27/47.54      inference('sup-', [status(thm)], ['49', '50'])).
% 47.27/47.54  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 47.27/47.54      inference('demod', [status(thm)], ['43', '48', '51'])).
% 47.27/47.54  thf('53', plain,
% 47.27/47.54      (![X13 : $i]:
% 47.27/47.54         (~ (v2_funct_1 @ X13)
% 47.27/47.54          | ((k5_relat_1 @ (k2_funct_1 @ X13) @ X13)
% 47.27/47.54              = (k6_partfun1 @ (k2_relat_1 @ X13)))
% 47.27/47.54          | ~ (v1_funct_1 @ X13)
% 47.27/47.54          | ~ (v1_relat_1 @ X13))),
% 47.27/47.54      inference('demod', [status(thm)], ['33', '34'])).
% 47.27/47.54  thf(dt_k6_partfun1, axiom,
% 47.27/47.54    (![A:$i]:
% 47.27/47.54     ( ( m1_subset_1 @
% 47.27/47.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 47.27/47.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 47.27/47.54  thf('54', plain,
% 47.27/47.54      (![X40 : $i]:
% 47.27/47.54         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 47.27/47.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 47.27/47.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 47.27/47.54  thf('55', plain,
% 47.27/47.54      (![X0 : $i]:
% 47.27/47.54         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 47.27/47.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 47.27/47.54          | ~ (v1_relat_1 @ X0)
% 47.27/47.54          | ~ (v1_funct_1 @ X0)
% 47.27/47.54          | ~ (v2_funct_1 @ X0))),
% 47.27/47.54      inference('sup+', [status(thm)], ['53', '54'])).
% 47.27/47.54  thf('56', plain,
% 47.27/47.54      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 47.27/47.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 47.27/47.54        | ~ (v2_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_relat_1 @ sk_B))),
% 47.27/47.54      inference('sup+', [status(thm)], ['52', '55'])).
% 47.27/47.54  thf('57', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 47.27/47.54      inference('demod', [status(thm)], ['43', '48', '51'])).
% 47.27/47.54  thf('58', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('59', plain,
% 47.27/47.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 47.27/47.54         (~ (v1_funct_1 @ X24)
% 47.27/47.54          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 47.27/47.54          | (v2_funct_1 @ X24)
% 47.27/47.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 47.27/47.54      inference('cnf', [status(esa)], [cc2_funct_2])).
% 47.27/47.54  thf('60', plain,
% 47.27/47.54      (((v2_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ~ (v1_funct_1 @ sk_B))),
% 47.27/47.54      inference('sup-', [status(thm)], ['58', '59'])).
% 47.27/47.54  thf('61', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 47.27/47.54  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['46', '47'])).
% 47.27/47.54  thf('66', plain,
% 47.27/47.54      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 47.27/47.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('demod', [status(thm)], ['56', '57', '63', '64', '65'])).
% 47.27/47.54  thf('67', plain,
% 47.27/47.54      (![X40 : $i]:
% 47.27/47.54         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 47.27/47.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 47.27/47.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 47.27/47.54  thf(redefinition_r2_relset_1, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i,D:$i]:
% 47.27/47.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 47.27/47.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 47.27/47.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 47.27/47.54  thf('68', plain,
% 47.27/47.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 47.27/47.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 47.27/47.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 47.27/47.54          | ((X20) = (X23))
% 47.27/47.54          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 47.27/47.54  thf('69', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i]:
% 47.27/47.54         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 47.27/47.54          | ((k6_partfun1 @ X0) = (X1))
% 47.27/47.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['67', '68'])).
% 47.27/47.54  thf('70', plain,
% 47.27/47.54      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 47.27/47.54        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 47.27/47.54             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['66', '69'])).
% 47.27/47.54  thf('71', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 47.27/47.54           (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 47.27/47.54        | ~ (v1_relat_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v2_funct_1 @ sk_B)
% 47.27/47.54        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['35', '70'])).
% 47.27/47.54  thf('72', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 47.27/47.54      inference('demod', [status(thm)], ['43', '48', '51'])).
% 47.27/47.54  thf('73', plain,
% 47.27/47.54      (![X40 : $i]:
% 47.27/47.54         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 47.27/47.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 47.27/47.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 47.27/47.54  thf('74', plain,
% 47.27/47.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 47.27/47.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 47.27/47.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 47.27/47.54          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 47.27/47.54          | ((X20) != (X23)))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 47.27/47.54  thf('75', plain,
% 47.27/47.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 47.27/47.54         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 47.27/47.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 47.27/47.54      inference('simplify', [status(thm)], ['74'])).
% 47.27/47.54  thf('76', plain,
% 47.27/47.54      (![X0 : $i]:
% 47.27/47.54         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 47.27/47.54      inference('sup-', [status(thm)], ['73', '75'])).
% 47.27/47.54  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['46', '47'])).
% 47.27/47.54  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('79', plain, ((v2_funct_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 47.27/47.54  thf('80', plain,
% 47.27/47.54      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['71', '72', '76', '77', '78', '79'])).
% 47.27/47.54  thf('81', plain,
% 47.27/47.54      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 47.27/47.54         = (k6_partfun1 @ sk_A))),
% 47.27/47.54      inference('demod', [status(thm)], ['31', '32', '80'])).
% 47.27/47.54  thf('82', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 47.27/47.54  thf('83', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54           (k6_partfun1 @ sk_A)))
% 47.27/47.54         <= (~
% 47.27/47.54             ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54               (k6_partfun1 @ sk_A))))),
% 47.27/47.54      inference('split', [status(esa)], ['0'])).
% 47.27/47.54  thf('84', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 47.27/47.54            sk_B) @ 
% 47.27/47.54           (k6_partfun1 @ sk_A)))
% 47.27/47.54         <= (~
% 47.27/47.54             ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54               (k6_partfun1 @ sk_A))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['82', '83'])).
% 47.27/47.54  thf('85', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 47.27/47.54           (k6_partfun1 @ sk_A)))
% 47.27/47.54         <= (~
% 47.27/47.54             ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54               (k6_partfun1 @ sk_A))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['81', '84'])).
% 47.27/47.54  thf('86', plain,
% 47.27/47.54      (![X0 : $i]:
% 47.27/47.54         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 47.27/47.54      inference('sup-', [status(thm)], ['73', '75'])).
% 47.27/47.54  thf('87', plain,
% 47.27/47.54      (((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54         (k6_partfun1 @ sk_A)))),
% 47.27/47.54      inference('demod', [status(thm)], ['85', '86'])).
% 47.27/47.54  thf('88', plain,
% 47.27/47.54      (~
% 47.27/47.54       ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 47.27/47.54         (k6_partfun1 @ sk_A))) | 
% 47.27/47.54       ~
% 47.27/47.54       ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 47.27/47.54          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 47.27/47.54         (k6_partfun1 @ sk_A)))),
% 47.27/47.54      inference('split', [status(esa)], ['0'])).
% 47.27/47.54  thf('89', plain,
% 47.27/47.54      (~
% 47.27/47.54       ((r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 47.27/47.54         (k6_partfun1 @ sk_A)))),
% 47.27/47.54      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 47.27/47.54  thf('90', plain,
% 47.27/47.54      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 47.27/47.54          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 47.27/47.54          (k6_partfun1 @ sk_A))),
% 47.27/47.54      inference('simpl_trail', [status(thm)], ['9', '89'])).
% 47.27/47.54  thf('91', plain,
% 47.27/47.54      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 47.27/47.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 47.27/47.54  thf('92', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 47.27/47.54  thf('93', plain,
% 47.27/47.54      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 47.27/47.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('demod', [status(thm)], ['91', '92'])).
% 47.27/47.54  thf('94', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('95', plain,
% 47.27/47.54      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 47.27/47.54         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 47.27/47.54          | ~ (v1_funct_1 @ X41)
% 47.27/47.54          | ~ (v1_funct_1 @ X44)
% 47.27/47.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 47.27/47.54          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 47.27/47.54              = (k5_relat_1 @ X41 @ X44)))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 47.27/47.54  thf('96', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.27/47.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 47.27/47.54            = (k5_relat_1 @ sk_B @ X0))
% 47.27/47.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.27/47.54          | ~ (v1_funct_1 @ X0)
% 47.27/47.54          | ~ (v1_funct_1 @ sk_B))),
% 47.27/47.54      inference('sup-', [status(thm)], ['94', '95'])).
% 47.27/47.54  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('98', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.27/47.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 47.27/47.54            = (k5_relat_1 @ sk_B @ X0))
% 47.27/47.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 47.27/47.54          | ~ (v1_funct_1 @ X0))),
% 47.27/47.54      inference('demod', [status(thm)], ['96', '97'])).
% 47.27/47.54  thf('99', plain,
% 47.27/47.54      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 47.27/47.54        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 47.27/47.54            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['93', '98'])).
% 47.27/47.54  thf('100', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 47.27/47.54  thf('101', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 47.27/47.54  thf('102', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['100', '101'])).
% 47.27/47.54  thf('103', plain,
% 47.27/47.54      (![X13 : $i]:
% 47.27/47.54         (~ (v2_funct_1 @ X13)
% 47.27/47.54          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 47.27/47.54              = (k6_relat_1 @ (k1_relat_1 @ X13)))
% 47.27/47.54          | ~ (v1_funct_1 @ X13)
% 47.27/47.54          | ~ (v1_relat_1 @ X13))),
% 47.27/47.54      inference('cnf', [status(esa)], [t61_funct_1])).
% 47.27/47.54  thf('104', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 47.27/47.54  thf('105', plain,
% 47.27/47.54      (![X13 : $i]:
% 47.27/47.54         (~ (v2_funct_1 @ X13)
% 47.27/47.54          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 47.27/47.54              = (k6_partfun1 @ (k1_relat_1 @ X13)))
% 47.27/47.54          | ~ (v1_funct_1 @ X13)
% 47.27/47.54          | ~ (v1_relat_1 @ X13))),
% 47.27/47.54      inference('demod', [status(thm)], ['103', '104'])).
% 47.27/47.54  thf('106', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(d1_funct_2, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i]:
% 47.27/47.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.27/47.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 47.27/47.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 47.27/47.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 47.27/47.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 47.27/47.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 47.27/47.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 47.27/47.54  thf(zf_stmt_1, axiom,
% 47.27/47.54    (![C:$i,B:$i,A:$i]:
% 47.27/47.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 47.27/47.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 47.27/47.54  thf('107', plain,
% 47.27/47.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 47.27/47.54         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 47.27/47.54          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 47.27/47.54          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 47.27/47.54  thf('108', plain,
% 47.27/47.54      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 47.27/47.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 47.27/47.54      inference('sup-', [status(thm)], ['106', '107'])).
% 47.27/47.54  thf('109', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 47.27/47.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 47.27/47.54  thf(zf_stmt_4, axiom,
% 47.27/47.54    (![B:$i,A:$i]:
% 47.27/47.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 47.27/47.54       ( zip_tseitin_0 @ B @ A ) ))).
% 47.27/47.54  thf(zf_stmt_5, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i]:
% 47.27/47.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.27/47.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 47.27/47.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 47.27/47.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 47.27/47.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 47.27/47.54  thf('110', plain,
% 47.27/47.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 47.27/47.54         (~ (zip_tseitin_0 @ X32 @ X33)
% 47.27/47.54          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 47.27/47.54          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 47.27/47.54  thf('111', plain,
% 47.27/47.54      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 47.27/47.54      inference('sup-', [status(thm)], ['109', '110'])).
% 47.27/47.54  thf('112', plain,
% 47.27/47.54      (![X27 : $i, X28 : $i]:
% 47.27/47.54         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 47.27/47.54  thf('113', plain,
% 47.27/47.54      (![X27 : $i, X28 : $i]:
% 47.27/47.54         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 47.27/47.54  thf('114', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 47.27/47.54      inference('simplify', [status(thm)], ['113'])).
% 47.27/47.54  thf('115', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.27/47.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 47.27/47.54      inference('sup+', [status(thm)], ['112', '114'])).
% 47.27/47.54  thf('116', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 47.27/47.54      inference('eq_fact', [status(thm)], ['115'])).
% 47.27/47.54  thf('117', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 47.27/47.54      inference('demod', [status(thm)], ['111', '116'])).
% 47.27/47.54  thf('118', plain,
% 47.27/47.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf(redefinition_k1_relset_1, axiom,
% 47.27/47.54    (![A:$i,B:$i,C:$i]:
% 47.27/47.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.27/47.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 47.27/47.54  thf('119', plain,
% 47.27/47.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 47.27/47.54         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 47.27/47.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 47.27/47.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 47.27/47.54  thf('120', plain,
% 47.27/47.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 47.27/47.54      inference('sup-', [status(thm)], ['118', '119'])).
% 47.27/47.54  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['108', '117', '120'])).
% 47.27/47.54  thf('122', plain,
% 47.27/47.54      (![X13 : $i]:
% 47.27/47.54         (~ (v2_funct_1 @ X13)
% 47.27/47.54          | ((k5_relat_1 @ X13 @ (k2_funct_1 @ X13))
% 47.27/47.54              = (k6_partfun1 @ (k1_relat_1 @ X13)))
% 47.27/47.54          | ~ (v1_funct_1 @ X13)
% 47.27/47.54          | ~ (v1_relat_1 @ X13))),
% 47.27/47.54      inference('demod', [status(thm)], ['103', '104'])).
% 47.27/47.54  thf('123', plain,
% 47.27/47.54      (![X40 : $i]:
% 47.27/47.54         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 47.27/47.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 47.27/47.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 47.27/47.54  thf('124', plain,
% 47.27/47.54      (![X0 : $i]:
% 47.27/47.54         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 47.27/47.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 47.27/47.54          | ~ (v1_relat_1 @ X0)
% 47.27/47.54          | ~ (v1_funct_1 @ X0)
% 47.27/47.54          | ~ (v2_funct_1 @ X0))),
% 47.27/47.54      inference('sup+', [status(thm)], ['122', '123'])).
% 47.27/47.54  thf('125', plain,
% 47.27/47.54      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 47.27/47.54         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 47.27/47.54        | ~ (v2_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v1_relat_1 @ sk_B))),
% 47.27/47.54      inference('sup+', [status(thm)], ['121', '124'])).
% 47.27/47.54  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['108', '117', '120'])).
% 47.27/47.54  thf('127', plain, ((v2_funct_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 47.27/47.54  thf('128', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('129', plain, ((v1_relat_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['46', '47'])).
% 47.27/47.54  thf('130', plain,
% 47.27/47.54      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 47.27/47.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 47.27/47.54      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 47.27/47.54  thf('131', plain,
% 47.27/47.54      (![X0 : $i, X1 : $i]:
% 47.27/47.54         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 47.27/47.54          | ((k6_partfun1 @ X0) = (X1))
% 47.27/47.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['67', '68'])).
% 47.27/47.54  thf('132', plain,
% 47.27/47.54      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 47.27/47.54        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 47.27/47.54             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['130', '131'])).
% 47.27/47.54  thf('133', plain,
% 47.27/47.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 47.27/47.54           (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 47.27/47.54        | ~ (v1_relat_1 @ sk_B)
% 47.27/47.54        | ~ (v1_funct_1 @ sk_B)
% 47.27/47.54        | ~ (v2_funct_1 @ sk_B)
% 47.27/47.54        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 47.27/47.54      inference('sup-', [status(thm)], ['105', '132'])).
% 47.27/47.54  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 47.27/47.54      inference('demod', [status(thm)], ['108', '117', '120'])).
% 47.27/47.54  thf('135', plain,
% 47.27/47.54      (![X0 : $i]:
% 47.27/47.54         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 47.27/47.54      inference('sup-', [status(thm)], ['73', '75'])).
% 47.27/47.54  thf('136', plain, ((v1_relat_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['46', '47'])).
% 47.27/47.54  thf('137', plain, ((v1_funct_1 @ sk_B)),
% 47.27/47.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.27/47.54  thf('138', plain, ((v2_funct_1 @ sk_B)),
% 47.27/47.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 47.27/47.54  thf('139', plain,
% 47.27/47.54      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 47.27/47.54      inference('demod', [status(thm)],
% 47.27/47.54                ['133', '134', '135', '136', '137', '138'])).
% 47.27/47.54  thf('140', plain,
% 47.27/47.54      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 47.27/47.54         = (k6_partfun1 @ sk_A))),
% 47.27/47.54      inference('demod', [status(thm)], ['99', '102', '139'])).
% 47.27/47.54  thf('141', plain,
% 47.27/47.54      (![X0 : $i]:
% 47.27/47.54         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 47.27/47.54      inference('sup-', [status(thm)], ['73', '75'])).
% 47.27/47.54  thf('142', plain, ($false),
% 47.27/47.54      inference('demod', [status(thm)], ['90', '140', '141'])).
% 47.27/47.54  
% 47.27/47.54  % SZS output end Refutation
% 47.27/47.54  
% 47.27/47.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
