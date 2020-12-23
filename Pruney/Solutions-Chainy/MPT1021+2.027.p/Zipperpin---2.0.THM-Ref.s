%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.al4vBQa4DE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:14 EST 2020

% Result     : Theorem 20.17s
% Output     : Refutation 20.17s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 598 expanded)
%              Number of leaves         :   47 ( 202 expanded)
%              Depth                    :   18
%              Number of atoms          : 1820 (11922 expanded)
%              Number of equality atoms :   72 ( 163 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('51',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('53',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_partfun1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    inference('sup-',[status(thm)],['44','45'])).

thf('68',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','65','66','67'])).

thf('69',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
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

thf('75',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('77',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('84',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','80','81','82','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','84'])).

thf('86',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('91',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('96',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('105',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('108',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
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

thf('111',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('115',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('117',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('118',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['116','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['119'])).

thf('121',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['115','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('123',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('124',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['112','121','124'])).

thf('126',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('127',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_partfun1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['112','121','124'])).

thf('131',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('132',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('134',plain,(
    r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('136',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('138',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['109','138'])).

thf('140',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['112','121','124'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('142',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('143',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('145',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','106','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['94','146','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.al4vBQa4DE
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 20.17/20.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.17/20.41  % Solved by: fo/fo7.sh
% 20.17/20.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.17/20.41  % done 5170 iterations in 19.973s
% 20.17/20.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.17/20.41  % SZS output start Refutation
% 20.17/20.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.17/20.41  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 20.17/20.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.17/20.41  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 20.17/20.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 20.17/20.41  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 20.17/20.41  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 20.17/20.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.17/20.41  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 20.17/20.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 20.17/20.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.17/20.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 20.17/20.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.17/20.41  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 20.17/20.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.17/20.41  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 20.17/20.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.17/20.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.17/20.41  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 20.17/20.41  thf(sk_B_type, type, sk_B: $i).
% 20.17/20.41  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 20.17/20.41  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 20.17/20.41  thf(sk_A_type, type, sk_A: $i).
% 20.17/20.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 20.17/20.41  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 20.17/20.41  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 20.17/20.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.17/20.41  thf(t88_funct_2, conjecture,
% 20.17/20.41    (![A:$i,B:$i]:
% 20.17/20.41     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 20.17/20.41         ( v3_funct_2 @ B @ A @ A ) & 
% 20.17/20.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 20.17/20.41       ( ( r2_relset_1 @
% 20.17/20.41           A @ A @ 
% 20.17/20.41           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 20.17/20.41           ( k6_partfun1 @ A ) ) & 
% 20.17/20.41         ( r2_relset_1 @
% 20.17/20.41           A @ A @ 
% 20.17/20.41           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 20.17/20.41           ( k6_partfun1 @ A ) ) ) ))).
% 20.17/20.41  thf(zf_stmt_0, negated_conjecture,
% 20.17/20.41    (~( ![A:$i,B:$i]:
% 20.17/20.41        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 20.17/20.41            ( v3_funct_2 @ B @ A @ A ) & 
% 20.17/20.41            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 20.17/20.41          ( ( r2_relset_1 @
% 20.17/20.41              A @ A @ 
% 20.17/20.41              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 20.17/20.41              ( k6_partfun1 @ A ) ) & 
% 20.17/20.41            ( r2_relset_1 @
% 20.17/20.41              A @ A @ 
% 20.17/20.41              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 20.17/20.41              ( k6_partfun1 @ A ) ) ) ) )),
% 20.17/20.41    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 20.17/20.41  thf('0', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 20.17/20.41           (k6_partfun1 @ sk_A))
% 20.17/20.41        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41             (k6_partfun1 @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('1', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 20.17/20.41           (k6_partfun1 @ sk_A)))
% 20.17/20.41         <= (~
% 20.17/20.41             ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 20.17/20.41               (k6_partfun1 @ sk_A))))),
% 20.17/20.41      inference('split', [status(esa)], ['0'])).
% 20.17/20.41  thf('2', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(redefinition_k2_funct_2, axiom,
% 20.17/20.41    (![A:$i,B:$i]:
% 20.17/20.41     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 20.17/20.41         ( v3_funct_2 @ B @ A @ A ) & 
% 20.17/20.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 20.17/20.41       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 20.17/20.41  thf('3', plain,
% 20.17/20.41      (![X47 : $i, X48 : $i]:
% 20.17/20.41         (((k2_funct_2 @ X48 @ X47) = (k2_funct_1 @ X47))
% 20.17/20.41          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))
% 20.17/20.41          | ~ (v3_funct_2 @ X47 @ X48 @ X48)
% 20.17/20.41          | ~ (v1_funct_2 @ X47 @ X48 @ X48)
% 20.17/20.41          | ~ (v1_funct_1 @ X47))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 20.17/20.41  thf('4', plain,
% 20.17/20.41      ((~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['2', '3'])).
% 20.17/20.41  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 20.17/20.41  thf('9', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41            (k2_funct_1 @ sk_B)) @ 
% 20.17/20.41           (k6_partfun1 @ sk_A)))
% 20.17/20.41         <= (~
% 20.17/20.41             ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 20.17/20.41               (k6_partfun1 @ sk_A))))),
% 20.17/20.41      inference('demod', [status(thm)], ['1', '8'])).
% 20.17/20.41  thf('10', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('11', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(dt_k2_funct_2, axiom,
% 20.17/20.41    (![A:$i,B:$i]:
% 20.17/20.41     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 20.17/20.41         ( v3_funct_2 @ B @ A @ A ) & 
% 20.17/20.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 20.17/20.41       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 20.17/20.41         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 20.17/20.41         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 20.17/20.41         ( m1_subset_1 @
% 20.17/20.41           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 20.17/20.41  thf('12', plain,
% 20.17/20.41      (![X39 : $i, X40 : $i]:
% 20.17/20.41         ((m1_subset_1 @ (k2_funct_2 @ X39 @ X40) @ 
% 20.17/20.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 20.17/20.41          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 20.17/20.41          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 20.17/20.41          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 20.17/20.41          | ~ (v1_funct_1 @ X40))),
% 20.17/20.41      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 20.17/20.41  thf('13', plain,
% 20.17/20.41      ((~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 20.17/20.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['11', '12'])).
% 20.17/20.41  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('17', plain,
% 20.17/20.41      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 20.17/20.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 20.17/20.41  thf(redefinition_k1_partfun1, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 20.17/20.41     ( ( ( v1_funct_1 @ E ) & 
% 20.17/20.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 20.17/20.41         ( v1_funct_1 @ F ) & 
% 20.17/20.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 20.17/20.41       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 20.17/20.41  thf('18', plain,
% 20.17/20.41      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 20.17/20.41         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 20.17/20.41          | ~ (v1_funct_1 @ X41)
% 20.17/20.41          | ~ (v1_funct_1 @ X44)
% 20.17/20.41          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 20.17/20.41          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 20.17/20.41              = (k5_relat_1 @ X41 @ X44)))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 20.17/20.41  thf('19', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.17/20.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 20.17/20.41            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 20.17/20.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 20.17/20.41          | ~ (v1_funct_1 @ X0)
% 20.17/20.41          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['17', '18'])).
% 20.17/20.41  thf('20', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('21', plain,
% 20.17/20.41      (![X39 : $i, X40 : $i]:
% 20.17/20.41         ((v1_funct_1 @ (k2_funct_2 @ X39 @ X40))
% 20.17/20.41          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 20.17/20.41          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 20.17/20.41          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 20.17/20.41          | ~ (v1_funct_1 @ X40))),
% 20.17/20.41      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 20.17/20.41  thf('22', plain,
% 20.17/20.41      ((~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['20', '21'])).
% 20.17/20.41  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('24', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('26', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 20.17/20.41  thf('27', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.17/20.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 20.17/20.41            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 20.17/20.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 20.17/20.41          | ~ (v1_funct_1 @ X0))),
% 20.17/20.41      inference('demod', [status(thm)], ['19', '26'])).
% 20.17/20.41  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 20.17/20.41  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 20.17/20.41  thf('30', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.17/20.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 20.17/20.41            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 20.17/20.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 20.17/20.41          | ~ (v1_funct_1 @ X0))),
% 20.17/20.41      inference('demod', [status(thm)], ['27', '28', '29'])).
% 20.17/20.41  thf('31', plain,
% 20.17/20.41      ((~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 20.17/20.41            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['10', '30'])).
% 20.17/20.41  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(t61_funct_1, axiom,
% 20.17/20.41    (![A:$i]:
% 20.17/20.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 20.17/20.41       ( ( v2_funct_1 @ A ) =>
% 20.17/20.41         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 20.17/20.41             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 20.17/20.41           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 20.17/20.41             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 20.17/20.41  thf('33', plain,
% 20.17/20.41      (![X11 : $i]:
% 20.17/20.41         (~ (v2_funct_1 @ X11)
% 20.17/20.41          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 20.17/20.41              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 20.17/20.41          | ~ (v1_funct_1 @ X11)
% 20.17/20.41          | ~ (v1_relat_1 @ X11))),
% 20.17/20.41      inference('cnf', [status(esa)], [t61_funct_1])).
% 20.17/20.41  thf(redefinition_k6_partfun1, axiom,
% 20.17/20.41    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 20.17/20.41  thf('34', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 20.17/20.41  thf('35', plain,
% 20.17/20.41      (![X11 : $i]:
% 20.17/20.41         (~ (v2_funct_1 @ X11)
% 20.17/20.41          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 20.17/20.41              = (k6_partfun1 @ (k2_relat_1 @ X11)))
% 20.17/20.41          | ~ (v1_funct_1 @ X11)
% 20.17/20.41          | ~ (v1_relat_1 @ X11))),
% 20.17/20.41      inference('demod', [status(thm)], ['33', '34'])).
% 20.17/20.41  thf('36', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(cc2_funct_2, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.17/20.41       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 20.17/20.41         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 20.17/20.41  thf('37', plain,
% 20.17/20.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 20.17/20.41         (~ (v1_funct_1 @ X26)
% 20.17/20.41          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 20.17/20.41          | (v2_funct_2 @ X26 @ X28)
% 20.17/20.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 20.17/20.41      inference('cnf', [status(esa)], [cc2_funct_2])).
% 20.17/20.41  thf('38', plain,
% 20.17/20.41      (((v2_funct_2 @ sk_B @ sk_A)
% 20.17/20.41        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ~ (v1_funct_1 @ sk_B))),
% 20.17/20.41      inference('sup-', [status(thm)], ['36', '37'])).
% 20.17/20.41  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 20.17/20.41      inference('demod', [status(thm)], ['38', '39', '40'])).
% 20.17/20.41  thf(d3_funct_2, axiom,
% 20.17/20.41    (![A:$i,B:$i]:
% 20.17/20.41     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 20.17/20.41       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 20.17/20.41  thf('42', plain,
% 20.17/20.41      (![X37 : $i, X38 : $i]:
% 20.17/20.41         (~ (v2_funct_2 @ X38 @ X37)
% 20.17/20.41          | ((k2_relat_1 @ X38) = (X37))
% 20.17/20.41          | ~ (v5_relat_1 @ X38 @ X37)
% 20.17/20.41          | ~ (v1_relat_1 @ X38))),
% 20.17/20.41      inference('cnf', [status(esa)], [d3_funct_2])).
% 20.17/20.41  thf('43', plain,
% 20.17/20.41      ((~ (v1_relat_1 @ sk_B)
% 20.17/20.41        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 20.17/20.41        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['41', '42'])).
% 20.17/20.41  thf('44', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(cc1_relset_1, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.17/20.41       ( v1_relat_1 @ C ) ))).
% 20.17/20.41  thf('45', plain,
% 20.17/20.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 20.17/20.41         ((v1_relat_1 @ X12)
% 20.17/20.41          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 20.17/20.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 20.17/20.41  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 20.17/20.41      inference('sup-', [status(thm)], ['44', '45'])).
% 20.17/20.41  thf('47', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(cc2_relset_1, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.17/20.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 20.17/20.41  thf('48', plain,
% 20.17/20.41      (![X15 : $i, X16 : $i, X17 : $i]:
% 20.17/20.41         ((v5_relat_1 @ X15 @ X17)
% 20.17/20.41          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 20.17/20.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.17/20.41  thf('49', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 20.17/20.41      inference('sup-', [status(thm)], ['47', '48'])).
% 20.17/20.41  thf('50', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['43', '46', '49'])).
% 20.17/20.41  thf('51', plain,
% 20.17/20.41      (![X11 : $i]:
% 20.17/20.41         (~ (v2_funct_1 @ X11)
% 20.17/20.41          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 20.17/20.41              = (k6_partfun1 @ (k2_relat_1 @ X11)))
% 20.17/20.41          | ~ (v1_funct_1 @ X11)
% 20.17/20.41          | ~ (v1_relat_1 @ X11))),
% 20.17/20.41      inference('demod', [status(thm)], ['33', '34'])).
% 20.17/20.41  thf(t29_relset_1, axiom,
% 20.17/20.41    (![A:$i]:
% 20.17/20.41     ( m1_subset_1 @
% 20.17/20.41       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 20.17/20.41  thf('52', plain,
% 20.17/20.41      (![X25 : $i]:
% 20.17/20.41         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 20.17/20.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 20.17/20.41      inference('cnf', [status(esa)], [t29_relset_1])).
% 20.17/20.41  thf('53', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 20.17/20.41  thf('54', plain,
% 20.17/20.41      (![X25 : $i]:
% 20.17/20.41         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 20.17/20.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 20.17/20.41      inference('demod', [status(thm)], ['52', '53'])).
% 20.17/20.41  thf(t3_subset, axiom,
% 20.17/20.41    (![A:$i,B:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 20.17/20.41  thf('55', plain,
% 20.17/20.41      (![X5 : $i, X6 : $i]:
% 20.17/20.41         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 20.17/20.41      inference('cnf', [status(esa)], [t3_subset])).
% 20.17/20.41  thf('56', plain,
% 20.17/20.41      (![X0 : $i]: (r1_tarski @ (k6_partfun1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 20.17/20.41      inference('sup-', [status(thm)], ['54', '55'])).
% 20.17/20.41  thf('57', plain,
% 20.17/20.41      (![X0 : $i]:
% 20.17/20.41         ((r1_tarski @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 20.17/20.41           (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 20.17/20.41          | ~ (v1_relat_1 @ X0)
% 20.17/20.41          | ~ (v1_funct_1 @ X0)
% 20.17/20.41          | ~ (v2_funct_1 @ X0))),
% 20.17/20.41      inference('sup+', [status(thm)], ['51', '56'])).
% 20.17/20.41  thf('58', plain,
% 20.17/20.41      (((r1_tarski @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 20.17/20.41         (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B)))
% 20.17/20.41        | ~ (v2_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_relat_1 @ sk_B))),
% 20.17/20.41      inference('sup+', [status(thm)], ['50', '57'])).
% 20.17/20.41  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['43', '46', '49'])).
% 20.17/20.41  thf('60', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('61', plain,
% 20.17/20.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 20.17/20.41         (~ (v1_funct_1 @ X26)
% 20.17/20.41          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 20.17/20.41          | (v2_funct_1 @ X26)
% 20.17/20.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 20.17/20.41      inference('cnf', [status(esa)], [cc2_funct_2])).
% 20.17/20.41  thf('62', plain,
% 20.17/20.41      (((v2_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ~ (v1_funct_1 @ sk_B))),
% 20.17/20.41      inference('sup-', [status(thm)], ['60', '61'])).
% 20.17/20.41  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 20.17/20.41      inference('demod', [status(thm)], ['62', '63', '64'])).
% 20.17/20.41  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 20.17/20.41      inference('sup-', [status(thm)], ['44', '45'])).
% 20.17/20.41  thf('68', plain,
% 20.17/20.41      ((r1_tarski @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 20.17/20.41        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 20.17/20.41  thf('69', plain,
% 20.17/20.41      (![X5 : $i, X7 : $i]:
% 20.17/20.41         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 20.17/20.41      inference('cnf', [status(esa)], [t3_subset])).
% 20.17/20.41  thf('70', plain,
% 20.17/20.41      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 20.17/20.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['68', '69'])).
% 20.17/20.41  thf('71', plain,
% 20.17/20.41      (![X25 : $i]:
% 20.17/20.41         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 20.17/20.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 20.17/20.41      inference('demod', [status(thm)], ['52', '53'])).
% 20.17/20.41  thf(redefinition_r2_relset_1, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i,D:$i]:
% 20.17/20.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 20.17/20.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.17/20.41       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 20.17/20.41  thf('72', plain,
% 20.17/20.41      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 20.17/20.41         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 20.17/20.41          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 20.17/20.41          | ((X21) = (X24))
% 20.17/20.41          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 20.17/20.41  thf('73', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i]:
% 20.17/20.41         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 20.17/20.41          | ((k6_partfun1 @ X0) = (X1))
% 20.17/20.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['71', '72'])).
% 20.17/20.41  thf('74', plain,
% 20.17/20.41      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 20.17/20.41        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 20.17/20.41             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['70', '73'])).
% 20.17/20.41  thf('75', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 20.17/20.41           (k6_partfun1 @ (k2_relat_1 @ sk_B)))
% 20.17/20.41        | ~ (v1_relat_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v2_funct_1 @ sk_B)
% 20.17/20.41        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['35', '74'])).
% 20.17/20.41  thf('76', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['43', '46', '49'])).
% 20.17/20.41  thf('77', plain,
% 20.17/20.41      (![X25 : $i]:
% 20.17/20.41         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 20.17/20.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 20.17/20.41      inference('demod', [status(thm)], ['52', '53'])).
% 20.17/20.41  thf('78', plain,
% 20.17/20.41      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 20.17/20.41         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 20.17/20.41          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 20.17/20.41          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 20.17/20.41          | ((X21) != (X24)))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 20.17/20.41  thf('79', plain,
% 20.17/20.41      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.17/20.41         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 20.17/20.41          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 20.17/20.41      inference('simplify', [status(thm)], ['78'])).
% 20.17/20.41  thf('80', plain,
% 20.17/20.41      (![X0 : $i]:
% 20.17/20.41         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 20.17/20.41      inference('sup-', [status(thm)], ['77', '79'])).
% 20.17/20.41  thf('81', plain, ((v1_relat_1 @ sk_B)),
% 20.17/20.41      inference('sup-', [status(thm)], ['44', '45'])).
% 20.17/20.41  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('83', plain, ((v2_funct_1 @ sk_B)),
% 20.17/20.41      inference('demod', [status(thm)], ['62', '63', '64'])).
% 20.17/20.41  thf('84', plain,
% 20.17/20.41      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['75', '76', '80', '81', '82', '83'])).
% 20.17/20.41  thf('85', plain,
% 20.17/20.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 20.17/20.41         = (k6_partfun1 @ sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['31', '32', '84'])).
% 20.17/20.41  thf('86', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 20.17/20.41  thf('87', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41           (k6_partfun1 @ sk_A)))
% 20.17/20.41         <= (~
% 20.17/20.41             ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41               (k6_partfun1 @ sk_A))))),
% 20.17/20.41      inference('split', [status(esa)], ['0'])).
% 20.17/20.41  thf('88', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 20.17/20.41            sk_B) @ 
% 20.17/20.41           (k6_partfun1 @ sk_A)))
% 20.17/20.41         <= (~
% 20.17/20.41             ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41               (k6_partfun1 @ sk_A))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['86', '87'])).
% 20.17/20.41  thf('89', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 20.17/20.41           (k6_partfun1 @ sk_A)))
% 20.17/20.41         <= (~
% 20.17/20.41             ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41               (k6_partfun1 @ sk_A))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['85', '88'])).
% 20.17/20.41  thf('90', plain,
% 20.17/20.41      (![X0 : $i]:
% 20.17/20.41         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 20.17/20.41      inference('sup-', [status(thm)], ['77', '79'])).
% 20.17/20.41  thf('91', plain,
% 20.17/20.41      (((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41         (k6_partfun1 @ sk_A)))),
% 20.17/20.41      inference('demod', [status(thm)], ['89', '90'])).
% 20.17/20.41  thf('92', plain,
% 20.17/20.41      (~
% 20.17/20.41       ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 20.17/20.41         (k6_partfun1 @ sk_A))) | 
% 20.17/20.41       ~
% 20.17/20.41       ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 20.17/20.41          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 20.17/20.41         (k6_partfun1 @ sk_A)))),
% 20.17/20.41      inference('split', [status(esa)], ['0'])).
% 20.17/20.41  thf('93', plain,
% 20.17/20.41      (~
% 20.17/20.41       ((r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 20.17/20.41         (k6_partfun1 @ sk_A)))),
% 20.17/20.41      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 20.17/20.41  thf('94', plain,
% 20.17/20.41      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 20.17/20.41          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 20.17/20.41          (k6_partfun1 @ sk_A))),
% 20.17/20.41      inference('simpl_trail', [status(thm)], ['9', '93'])).
% 20.17/20.41  thf('95', plain,
% 20.17/20.41      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 20.17/20.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 20.17/20.41  thf('96', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 20.17/20.41  thf('97', plain,
% 20.17/20.41      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 20.17/20.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('demod', [status(thm)], ['95', '96'])).
% 20.17/20.41  thf('98', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('99', plain,
% 20.17/20.41      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 20.17/20.41         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 20.17/20.41          | ~ (v1_funct_1 @ X41)
% 20.17/20.41          | ~ (v1_funct_1 @ X44)
% 20.17/20.41          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 20.17/20.41          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 20.17/20.41              = (k5_relat_1 @ X41 @ X44)))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 20.17/20.41  thf('100', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.17/20.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 20.17/20.41            = (k5_relat_1 @ sk_B @ X0))
% 20.17/20.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 20.17/20.41          | ~ (v1_funct_1 @ X0)
% 20.17/20.41          | ~ (v1_funct_1 @ sk_B))),
% 20.17/20.41      inference('sup-', [status(thm)], ['98', '99'])).
% 20.17/20.41  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('102', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.17/20.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 20.17/20.41            = (k5_relat_1 @ sk_B @ X0))
% 20.17/20.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 20.17/20.41          | ~ (v1_funct_1 @ X0))),
% 20.17/20.41      inference('demod', [status(thm)], ['100', '101'])).
% 20.17/20.41  thf('103', plain,
% 20.17/20.41      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 20.17/20.41        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 20.17/20.41            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['97', '102'])).
% 20.17/20.41  thf('104', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 20.17/20.41  thf('105', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 20.17/20.41  thf('106', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['104', '105'])).
% 20.17/20.41  thf('107', plain,
% 20.17/20.41      (![X11 : $i]:
% 20.17/20.41         (~ (v2_funct_1 @ X11)
% 20.17/20.41          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 20.17/20.41              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 20.17/20.41          | ~ (v1_funct_1 @ X11)
% 20.17/20.41          | ~ (v1_relat_1 @ X11))),
% 20.17/20.41      inference('cnf', [status(esa)], [t61_funct_1])).
% 20.17/20.41  thf('108', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 20.17/20.41  thf('109', plain,
% 20.17/20.41      (![X11 : $i]:
% 20.17/20.41         (~ (v2_funct_1 @ X11)
% 20.17/20.41          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 20.17/20.41              = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 20.17/20.41          | ~ (v1_funct_1 @ X11)
% 20.17/20.41          | ~ (v1_relat_1 @ X11))),
% 20.17/20.41      inference('demod', [status(thm)], ['107', '108'])).
% 20.17/20.41  thf('110', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(d1_funct_2, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.17/20.41       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.17/20.41           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 20.17/20.41             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 20.17/20.41         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.17/20.41           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 20.17/20.41             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 20.17/20.41  thf(zf_stmt_1, axiom,
% 20.17/20.41    (![C:$i,B:$i,A:$i]:
% 20.17/20.41     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 20.17/20.41       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 20.17/20.41  thf('111', plain,
% 20.17/20.41      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.17/20.41         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 20.17/20.41          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 20.17/20.41          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.17/20.41  thf('112', plain,
% 20.17/20.41      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 20.17/20.41        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['110', '111'])).
% 20.17/20.41  thf('113', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 20.17/20.41  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 20.17/20.41  thf(zf_stmt_4, axiom,
% 20.17/20.41    (![B:$i,A:$i]:
% 20.17/20.41     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.17/20.41       ( zip_tseitin_0 @ B @ A ) ))).
% 20.17/20.41  thf(zf_stmt_5, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.17/20.41       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 20.17/20.41         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.17/20.41           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 20.17/20.41             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 20.17/20.41  thf('114', plain,
% 20.17/20.41      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.17/20.41         (~ (zip_tseitin_0 @ X34 @ X35)
% 20.17/20.41          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 20.17/20.41          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 20.17/20.41  thf('115', plain,
% 20.17/20.41      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 20.17/20.41      inference('sup-', [status(thm)], ['113', '114'])).
% 20.17/20.41  thf('116', plain,
% 20.17/20.41      (![X29 : $i, X30 : $i]:
% 20.17/20.41         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.17/20.41  thf('117', plain,
% 20.17/20.41      (![X29 : $i, X30 : $i]:
% 20.17/20.41         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.17/20.41  thf('118', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 20.17/20.41      inference('simplify', [status(thm)], ['117'])).
% 20.17/20.41  thf('119', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.17/20.41         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 20.17/20.41      inference('sup+', [status(thm)], ['116', '118'])).
% 20.17/20.41  thf('120', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 20.17/20.41      inference('eq_fact', [status(thm)], ['119'])).
% 20.17/20.41  thf('121', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 20.17/20.41      inference('demod', [status(thm)], ['115', '120'])).
% 20.17/20.41  thf('122', plain,
% 20.17/20.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf(redefinition_k1_relset_1, axiom,
% 20.17/20.41    (![A:$i,B:$i,C:$i]:
% 20.17/20.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.17/20.41       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 20.17/20.41  thf('123', plain,
% 20.17/20.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 20.17/20.41         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 20.17/20.41          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 20.17/20.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 20.17/20.41  thf('124', plain,
% 20.17/20.41      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 20.17/20.41      inference('sup-', [status(thm)], ['122', '123'])).
% 20.17/20.41  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['112', '121', '124'])).
% 20.17/20.41  thf('126', plain,
% 20.17/20.41      (![X11 : $i]:
% 20.17/20.41         (~ (v2_funct_1 @ X11)
% 20.17/20.41          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 20.17/20.41              = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 20.17/20.41          | ~ (v1_funct_1 @ X11)
% 20.17/20.41          | ~ (v1_relat_1 @ X11))),
% 20.17/20.41      inference('demod', [status(thm)], ['107', '108'])).
% 20.17/20.41  thf('127', plain,
% 20.17/20.41      (![X0 : $i]: (r1_tarski @ (k6_partfun1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 20.17/20.41      inference('sup-', [status(thm)], ['54', '55'])).
% 20.17/20.41  thf('128', plain,
% 20.17/20.41      (![X0 : $i]:
% 20.17/20.41         ((r1_tarski @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 20.17/20.41           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 20.17/20.41          | ~ (v1_relat_1 @ X0)
% 20.17/20.41          | ~ (v1_funct_1 @ X0)
% 20.17/20.41          | ~ (v2_funct_1 @ X0))),
% 20.17/20.41      inference('sup+', [status(thm)], ['126', '127'])).
% 20.17/20.41  thf('129', plain,
% 20.17/20.41      (((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 20.17/20.41         (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 20.17/20.41        | ~ (v2_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v1_relat_1 @ sk_B))),
% 20.17/20.41      inference('sup+', [status(thm)], ['125', '128'])).
% 20.17/20.41  thf('130', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['112', '121', '124'])).
% 20.17/20.41  thf('131', plain, ((v2_funct_1 @ sk_B)),
% 20.17/20.41      inference('demod', [status(thm)], ['62', '63', '64'])).
% 20.17/20.41  thf('132', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('133', plain, ((v1_relat_1 @ sk_B)),
% 20.17/20.41      inference('sup-', [status(thm)], ['44', '45'])).
% 20.17/20.41  thf('134', plain,
% 20.17/20.41      ((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 20.17/20.41        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 20.17/20.41  thf('135', plain,
% 20.17/20.41      (![X5 : $i, X7 : $i]:
% 20.17/20.41         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 20.17/20.41      inference('cnf', [status(esa)], [t3_subset])).
% 20.17/20.41  thf('136', plain,
% 20.17/20.41      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 20.17/20.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 20.17/20.41      inference('sup-', [status(thm)], ['134', '135'])).
% 20.17/20.41  thf('137', plain,
% 20.17/20.41      (![X0 : $i, X1 : $i]:
% 20.17/20.41         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 20.17/20.41          | ((k6_partfun1 @ X0) = (X1))
% 20.17/20.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['71', '72'])).
% 20.17/20.41  thf('138', plain,
% 20.17/20.41      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 20.17/20.41        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 20.17/20.41             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['136', '137'])).
% 20.17/20.41  thf('139', plain,
% 20.17/20.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 20.17/20.41           (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 20.17/20.41        | ~ (v1_relat_1 @ sk_B)
% 20.17/20.41        | ~ (v1_funct_1 @ sk_B)
% 20.17/20.41        | ~ (v2_funct_1 @ sk_B)
% 20.17/20.41        | ((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 20.17/20.41      inference('sup-', [status(thm)], ['109', '138'])).
% 20.17/20.41  thf('140', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 20.17/20.41      inference('demod', [status(thm)], ['112', '121', '124'])).
% 20.17/20.41  thf('141', plain,
% 20.17/20.41      (![X0 : $i]:
% 20.17/20.41         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 20.17/20.41      inference('sup-', [status(thm)], ['77', '79'])).
% 20.17/20.41  thf('142', plain, ((v1_relat_1 @ sk_B)),
% 20.17/20.41      inference('sup-', [status(thm)], ['44', '45'])).
% 20.17/20.41  thf('143', plain, ((v1_funct_1 @ sk_B)),
% 20.17/20.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.17/20.41  thf('144', plain, ((v2_funct_1 @ sk_B)),
% 20.17/20.41      inference('demod', [status(thm)], ['62', '63', '64'])).
% 20.17/20.41  thf('145', plain,
% 20.17/20.41      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 20.17/20.41      inference('demod', [status(thm)],
% 20.17/20.41                ['139', '140', '141', '142', '143', '144'])).
% 20.17/20.41  thf('146', plain,
% 20.17/20.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 20.17/20.41         = (k6_partfun1 @ sk_A))),
% 20.17/20.41      inference('demod', [status(thm)], ['103', '106', '145'])).
% 20.17/20.41  thf('147', plain,
% 20.17/20.41      (![X0 : $i]:
% 20.17/20.41         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 20.17/20.41      inference('sup-', [status(thm)], ['77', '79'])).
% 20.17/20.41  thf('148', plain, ($false),
% 20.17/20.41      inference('demod', [status(thm)], ['94', '146', '147'])).
% 20.17/20.41  
% 20.17/20.41  % SZS output end Refutation
% 20.17/20.41  
% 20.17/20.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
