%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LfwYM63Pfe

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:14 EST 2020

% Result     : Theorem 30.57s
% Output     : Refutation 30.57s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 580 expanded)
%              Number of leaves         :   46 ( 196 expanded)
%              Depth                    :   17
%              Number of atoms          : 1807 (11854 expanded)
%              Number of equality atoms :   70 ( 155 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( ( k2_funct_2 @ X41 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

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
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3 ) @ X3 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_2 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_2 @ X29 @ X28 )
      | ( ( k2_relat_1 @ X29 )
        = X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3 ) @ X3 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('52',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    inference('sup-',[status(thm)],['44','45'])).

thf('66',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','63','64','65'])).

thf('67',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
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
    inference(demod,[status(thm)],['43','46','49'])).

thf('73',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('94',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('103',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('104',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('111',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('113',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('114',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('123',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

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
    inference('sup-',[status(thm)],['44','45'])).

thf('130',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('132',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','132'])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['108','117','120'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('136',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('137',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('139',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138'])).

thf('140',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','104','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['92','140','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LfwYM63Pfe
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 30.57/30.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.57/30.80  % Solved by: fo/fo7.sh
% 30.57/30.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.57/30.80  % done 9596 iterations in 30.352s
% 30.57/30.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.57/30.80  % SZS output start Refutation
% 30.57/30.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 30.57/30.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 30.57/30.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 30.57/30.80  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 30.57/30.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 30.57/30.80  thf(sk_B_type, type, sk_B: $i).
% 30.57/30.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 30.57/30.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.57/30.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 30.57/30.80  thf(sk_A_type, type, sk_A: $i).
% 30.57/30.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 30.57/30.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 30.57/30.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.57/30.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 30.57/30.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.57/30.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 30.57/30.80  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 30.57/30.80  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 30.57/30.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.57/30.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.57/30.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.57/30.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.57/30.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 30.57/30.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 30.57/30.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 30.57/30.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 30.57/30.80  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 30.57/30.80  thf(t88_funct_2, conjecture,
% 30.57/30.80    (![A:$i,B:$i]:
% 30.57/30.80     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 30.57/30.80         ( v3_funct_2 @ B @ A @ A ) & 
% 30.57/30.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 30.57/30.80       ( ( r2_relset_1 @
% 30.57/30.80           A @ A @ 
% 30.57/30.80           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 30.57/30.80           ( k6_partfun1 @ A ) ) & 
% 30.57/30.80         ( r2_relset_1 @
% 30.57/30.80           A @ A @ 
% 30.57/30.80           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 30.57/30.80           ( k6_partfun1 @ A ) ) ) ))).
% 30.57/30.80  thf(zf_stmt_0, negated_conjecture,
% 30.57/30.80    (~( ![A:$i,B:$i]:
% 30.57/30.80        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 30.57/30.80            ( v3_funct_2 @ B @ A @ A ) & 
% 30.57/30.80            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 30.57/30.80          ( ( r2_relset_1 @
% 30.57/30.80              A @ A @ 
% 30.57/30.80              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 30.57/30.80              ( k6_partfun1 @ A ) ) & 
% 30.57/30.80            ( r2_relset_1 @
% 30.57/30.80              A @ A @ 
% 30.57/30.80              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 30.57/30.80              ( k6_partfun1 @ A ) ) ) ) )),
% 30.57/30.80    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 30.57/30.80  thf('0', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80           (k6_partfun1 @ sk_A))
% 30.57/30.80        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80             (k6_partfun1 @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('1', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80           (k6_partfun1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('split', [status(esa)], ['0'])).
% 30.57/30.80  thf(redefinition_k6_partfun1, axiom,
% 30.57/30.80    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 30.57/30.80  thf('2', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.57/30.80  thf('3', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80           (k6_relat_1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('demod', [status(thm)], ['1', '2'])).
% 30.57/30.80  thf('4', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(redefinition_k2_funct_2, axiom,
% 30.57/30.80    (![A:$i,B:$i]:
% 30.57/30.80     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 30.57/30.80         ( v3_funct_2 @ B @ A @ A ) & 
% 30.57/30.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 30.57/30.80       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 30.57/30.80  thf('5', plain,
% 30.57/30.80      (![X40 : $i, X41 : $i]:
% 30.57/30.80         (((k2_funct_2 @ X41 @ X40) = (k2_funct_1 @ X40))
% 30.57/30.80          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 30.57/30.80          | ~ (v3_funct_2 @ X40 @ X41 @ X41)
% 30.57/30.80          | ~ (v1_funct_2 @ X40 @ X41 @ X41)
% 30.57/30.80          | ~ (v1_funct_1 @ X40))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 30.57/30.80  thf('6', plain,
% 30.57/30.80      ((~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['4', '5'])).
% 30.57/30.80  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 30.57/30.80  thf('11', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80            (k2_funct_1 @ sk_B)) @ 
% 30.57/30.80           (k6_relat_1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('demod', [status(thm)], ['3', '10'])).
% 30.57/30.80  thf('12', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('13', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(dt_k2_funct_2, axiom,
% 30.57/30.80    (![A:$i,B:$i]:
% 30.57/30.80     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 30.57/30.80         ( v3_funct_2 @ B @ A @ A ) & 
% 30.57/30.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 30.57/30.80       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 30.57/30.80         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 30.57/30.80         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 30.57/30.80         ( m1_subset_1 @
% 30.57/30.80           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 30.57/30.80  thf('14', plain,
% 30.57/30.80      (![X30 : $i, X31 : $i]:
% 30.57/30.80         ((m1_subset_1 @ (k2_funct_2 @ X30 @ X31) @ 
% 30.57/30.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 30.57/30.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 30.57/30.80          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 30.57/30.80          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 30.57/30.80          | ~ (v1_funct_1 @ X31))),
% 30.57/30.80      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 30.57/30.80  thf('15', plain,
% 30.57/30.80      ((~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 30.57/30.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['13', '14'])).
% 30.57/30.80  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('19', plain,
% 30.57/30.80      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 30.57/30.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 30.57/30.80  thf(redefinition_k1_partfun1, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.57/30.80     ( ( ( v1_funct_1 @ E ) & 
% 30.57/30.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.57/30.80         ( v1_funct_1 @ F ) & 
% 30.57/30.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.57/30.80       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 30.57/30.80  thf('20', plain,
% 30.57/30.80      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 30.57/30.80         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 30.57/30.80          | ~ (v1_funct_1 @ X34)
% 30.57/30.80          | ~ (v1_funct_1 @ X37)
% 30.57/30.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 30.57/30.80          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 30.57/30.80              = (k5_relat_1 @ X34 @ X37)))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 30.57/30.80  thf('21', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.57/30.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 30.57/30.80            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 30.57/30.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.57/30.80          | ~ (v1_funct_1 @ X0)
% 30.57/30.80          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['19', '20'])).
% 30.57/30.80  thf('22', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('23', plain,
% 30.57/30.80      (![X30 : $i, X31 : $i]:
% 30.57/30.80         ((v1_funct_1 @ (k2_funct_2 @ X30 @ X31))
% 30.57/30.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 30.57/30.80          | ~ (v3_funct_2 @ X31 @ X30 @ X30)
% 30.57/30.80          | ~ (v1_funct_2 @ X31 @ X30 @ X30)
% 30.57/30.80          | ~ (v1_funct_1 @ X31))),
% 30.57/30.80      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 30.57/30.80  thf('24', plain,
% 30.57/30.80      ((~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['22', '23'])).
% 30.57/30.80  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('26', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('28', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 30.57/30.80  thf('29', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.57/30.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 30.57/30.80            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 30.57/30.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.57/30.80          | ~ (v1_funct_1 @ X0))),
% 30.57/30.80      inference('demod', [status(thm)], ['21', '28'])).
% 30.57/30.80  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 30.57/30.80  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 30.57/30.80  thf('32', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.57/30.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 30.57/30.80            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 30.57/30.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.57/30.80          | ~ (v1_funct_1 @ X0))),
% 30.57/30.80      inference('demod', [status(thm)], ['29', '30', '31'])).
% 30.57/30.80  thf('33', plain,
% 30.57/30.80      ((~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 30.57/30.80            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['12', '32'])).
% 30.57/30.80  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(t61_funct_1, axiom,
% 30.57/30.80    (![A:$i]:
% 30.57/30.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.57/30.80       ( ( v2_funct_1 @ A ) =>
% 30.57/30.80         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 30.57/30.80             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 30.57/30.80           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 30.57/30.80             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 30.57/30.80  thf('35', plain,
% 30.57/30.80      (![X3 : $i]:
% 30.57/30.80         (~ (v2_funct_1 @ X3)
% 30.57/30.80          | ((k5_relat_1 @ (k2_funct_1 @ X3) @ X3)
% 30.57/30.80              = (k6_relat_1 @ (k2_relat_1 @ X3)))
% 30.57/30.80          | ~ (v1_funct_1 @ X3)
% 30.57/30.80          | ~ (v1_relat_1 @ X3))),
% 30.57/30.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 30.57/30.80  thf('36', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(cc2_funct_2, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i]:
% 30.57/30.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.57/30.80       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 30.57/30.80         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 30.57/30.80  thf('37', plain,
% 30.57/30.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 30.57/30.80         (~ (v1_funct_1 @ X17)
% 30.57/30.80          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 30.57/30.80          | (v2_funct_2 @ X17 @ X19)
% 30.57/30.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 30.57/30.80      inference('cnf', [status(esa)], [cc2_funct_2])).
% 30.57/30.80  thf('38', plain,
% 30.57/30.80      (((v2_funct_2 @ sk_B @ sk_A)
% 30.57/30.80        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ~ (v1_funct_1 @ sk_B))),
% 30.57/30.80      inference('sup-', [status(thm)], ['36', '37'])).
% 30.57/30.80  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 30.57/30.80      inference('demod', [status(thm)], ['38', '39', '40'])).
% 30.57/30.80  thf(d3_funct_2, axiom,
% 30.57/30.80    (![A:$i,B:$i]:
% 30.57/30.80     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 30.57/30.80       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 30.57/30.80  thf('42', plain,
% 30.57/30.80      (![X28 : $i, X29 : $i]:
% 30.57/30.80         (~ (v2_funct_2 @ X29 @ X28)
% 30.57/30.80          | ((k2_relat_1 @ X29) = (X28))
% 30.57/30.80          | ~ (v5_relat_1 @ X29 @ X28)
% 30.57/30.80          | ~ (v1_relat_1 @ X29))),
% 30.57/30.80      inference('cnf', [status(esa)], [d3_funct_2])).
% 30.57/30.80  thf('43', plain,
% 30.57/30.80      ((~ (v1_relat_1 @ sk_B)
% 30.57/30.80        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 30.57/30.80        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['41', '42'])).
% 30.57/30.80  thf('44', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(cc1_relset_1, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i]:
% 30.57/30.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.57/30.80       ( v1_relat_1 @ C ) ))).
% 30.57/30.80  thf('45', plain,
% 30.57/30.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 30.57/30.80         ((v1_relat_1 @ X4)
% 30.57/30.80          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 30.57/30.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.57/30.80  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 30.57/30.80      inference('sup-', [status(thm)], ['44', '45'])).
% 30.57/30.80  thf('47', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(cc2_relset_1, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i]:
% 30.57/30.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.57/30.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 30.57/30.80  thf('48', plain,
% 30.57/30.80      (![X7 : $i, X8 : $i, X9 : $i]:
% 30.57/30.80         ((v5_relat_1 @ X7 @ X9)
% 30.57/30.80          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 30.57/30.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 30.57/30.80  thf('49', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 30.57/30.80      inference('sup-', [status(thm)], ['47', '48'])).
% 30.57/30.80  thf('50', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 30.57/30.80      inference('demod', [status(thm)], ['43', '46', '49'])).
% 30.57/30.80  thf('51', plain,
% 30.57/30.80      (![X3 : $i]:
% 30.57/30.80         (~ (v2_funct_1 @ X3)
% 30.57/30.80          | ((k5_relat_1 @ (k2_funct_1 @ X3) @ X3)
% 30.57/30.80              = (k6_relat_1 @ (k2_relat_1 @ X3)))
% 30.57/30.80          | ~ (v1_funct_1 @ X3)
% 30.57/30.80          | ~ (v1_relat_1 @ X3))),
% 30.57/30.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 30.57/30.80  thf(dt_k6_partfun1, axiom,
% 30.57/30.80    (![A:$i]:
% 30.57/30.80     ( ( m1_subset_1 @
% 30.57/30.80         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 30.57/30.80       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 30.57/30.80  thf('52', plain,
% 30.57/30.80      (![X33 : $i]:
% 30.57/30.80         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 30.57/30.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 30.57/30.80      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 30.57/30.80  thf('53', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.57/30.80  thf('54', plain,
% 30.57/30.80      (![X33 : $i]:
% 30.57/30.80         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 30.57/30.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 30.57/30.80      inference('demod', [status(thm)], ['52', '53'])).
% 30.57/30.80  thf('55', plain,
% 30.57/30.80      (![X0 : $i]:
% 30.57/30.80         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 30.57/30.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 30.57/30.80          | ~ (v1_relat_1 @ X0)
% 30.57/30.80          | ~ (v1_funct_1 @ X0)
% 30.57/30.80          | ~ (v2_funct_1 @ X0))),
% 30.57/30.80      inference('sup+', [status(thm)], ['51', '54'])).
% 30.57/30.80  thf('56', plain,
% 30.57/30.80      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 30.57/30.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 30.57/30.80        | ~ (v2_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_relat_1 @ sk_B))),
% 30.57/30.80      inference('sup+', [status(thm)], ['50', '55'])).
% 30.57/30.80  thf('57', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 30.57/30.80      inference('demod', [status(thm)], ['43', '46', '49'])).
% 30.57/30.80  thf('58', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('59', plain,
% 30.57/30.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 30.57/30.80         (~ (v1_funct_1 @ X17)
% 30.57/30.80          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 30.57/30.80          | (v2_funct_1 @ X17)
% 30.57/30.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 30.57/30.80      inference('cnf', [status(esa)], [cc2_funct_2])).
% 30.57/30.80  thf('60', plain,
% 30.57/30.80      (((v2_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ~ (v1_funct_1 @ sk_B))),
% 30.57/30.80      inference('sup-', [status(thm)], ['58', '59'])).
% 30.57/30.80  thf('61', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 30.57/30.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 30.57/30.80  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 30.57/30.80      inference('sup-', [status(thm)], ['44', '45'])).
% 30.57/30.80  thf('66', plain,
% 30.57/30.80      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 30.57/30.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('demod', [status(thm)], ['56', '57', '63', '64', '65'])).
% 30.57/30.80  thf('67', plain,
% 30.57/30.80      (![X33 : $i]:
% 30.57/30.80         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 30.57/30.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 30.57/30.80      inference('demod', [status(thm)], ['52', '53'])).
% 30.57/30.80  thf(redefinition_r2_relset_1, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i,D:$i]:
% 30.57/30.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.57/30.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.57/30.80       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 30.57/30.80  thf('68', plain,
% 30.57/30.80      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 30.57/30.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 30.57/30.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 30.57/30.80          | ((X13) = (X16))
% 30.57/30.80          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.57/30.80  thf('69', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i]:
% 30.57/30.80         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 30.57/30.80          | ((k6_relat_1 @ X0) = (X1))
% 30.57/30.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['67', '68'])).
% 30.57/30.80  thf('70', plain,
% 30.57/30.80      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 30.57/30.80        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 30.57/30.80             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['66', '69'])).
% 30.57/30.80  thf('71', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 30.57/30.80           (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 30.57/30.80        | ~ (v1_relat_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v2_funct_1 @ sk_B)
% 30.57/30.80        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['35', '70'])).
% 30.57/30.80  thf('72', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 30.57/30.80      inference('demod', [status(thm)], ['43', '46', '49'])).
% 30.57/30.80  thf('73', plain,
% 30.57/30.80      (![X33 : $i]:
% 30.57/30.80         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 30.57/30.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 30.57/30.80      inference('demod', [status(thm)], ['52', '53'])).
% 30.57/30.80  thf('74', plain,
% 30.57/30.80      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 30.57/30.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 30.57/30.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 30.57/30.80          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 30.57/30.80          | ((X13) != (X16)))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.57/30.80  thf('75', plain,
% 30.57/30.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 30.57/30.80         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 30.57/30.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 30.57/30.80      inference('simplify', [status(thm)], ['74'])).
% 30.57/30.80  thf('76', plain,
% 30.57/30.80      (![X0 : $i]:
% 30.57/30.80         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 30.57/30.80      inference('sup-', [status(thm)], ['73', '75'])).
% 30.57/30.80  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 30.57/30.80      inference('sup-', [status(thm)], ['44', '45'])).
% 30.57/30.80  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('79', plain, ((v2_funct_1 @ sk_B)),
% 30.57/30.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 30.57/30.80  thf('80', plain,
% 30.57/30.80      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['71', '72', '76', '77', '78', '79'])).
% 30.57/30.80  thf('81', plain,
% 30.57/30.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 30.57/30.80         = (k6_relat_1 @ sk_A))),
% 30.57/30.80      inference('demod', [status(thm)], ['33', '34', '80'])).
% 30.57/30.80  thf('82', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 30.57/30.80  thf('83', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80           (k6_partfun1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('split', [status(esa)], ['0'])).
% 30.57/30.80  thf('84', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.57/30.80  thf('85', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80           (k6_relat_1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('demod', [status(thm)], ['83', '84'])).
% 30.57/30.80  thf('86', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 30.57/30.80            sk_B) @ 
% 30.57/30.80           (k6_relat_1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['82', '85'])).
% 30.57/30.80  thf('87', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 30.57/30.80           (k6_relat_1 @ sk_A)))
% 30.57/30.80         <= (~
% 30.57/30.80             ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80               (k6_partfun1 @ sk_A))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['81', '86'])).
% 30.57/30.80  thf('88', plain,
% 30.57/30.80      (![X0 : $i]:
% 30.57/30.80         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 30.57/30.80      inference('sup-', [status(thm)], ['73', '75'])).
% 30.57/30.80  thf('89', plain,
% 30.57/30.80      (((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80         (k6_partfun1 @ sk_A)))),
% 30.57/30.80      inference('demod', [status(thm)], ['87', '88'])).
% 30.57/30.80  thf('90', plain,
% 30.57/30.80      (~
% 30.57/30.80       ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80         (k6_partfun1 @ sk_A))) | 
% 30.57/30.80       ~
% 30.57/30.80       ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 30.57/30.80          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 30.57/30.80         (k6_partfun1 @ sk_A)))),
% 30.57/30.80      inference('split', [status(esa)], ['0'])).
% 30.57/30.80  thf('91', plain,
% 30.57/30.80      (~
% 30.57/30.80       ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 30.57/30.80         (k6_partfun1 @ sk_A)))),
% 30.57/30.80      inference('sat_resolution*', [status(thm)], ['89', '90'])).
% 30.57/30.80  thf('92', plain,
% 30.57/30.80      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.57/30.80          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 30.57/30.80          (k6_relat_1 @ sk_A))),
% 30.57/30.80      inference('simpl_trail', [status(thm)], ['11', '91'])).
% 30.57/30.80  thf('93', plain,
% 30.57/30.80      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 30.57/30.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 30.57/30.80  thf('94', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 30.57/30.80  thf('95', plain,
% 30.57/30.80      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 30.57/30.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('demod', [status(thm)], ['93', '94'])).
% 30.57/30.80  thf('96', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('97', plain,
% 30.57/30.80      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 30.57/30.80         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 30.57/30.80          | ~ (v1_funct_1 @ X34)
% 30.57/30.80          | ~ (v1_funct_1 @ X37)
% 30.57/30.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 30.57/30.80          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 30.57/30.80              = (k5_relat_1 @ X34 @ X37)))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 30.57/30.80  thf('98', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.57/30.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 30.57/30.80            = (k5_relat_1 @ sk_B @ X0))
% 30.57/30.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.57/30.80          | ~ (v1_funct_1 @ X0)
% 30.57/30.80          | ~ (v1_funct_1 @ sk_B))),
% 30.57/30.80      inference('sup-', [status(thm)], ['96', '97'])).
% 30.57/30.80  thf('99', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('100', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.57/30.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 30.57/30.80            = (k5_relat_1 @ sk_B @ X0))
% 30.57/30.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.57/30.80          | ~ (v1_funct_1 @ X0))),
% 30.57/30.80      inference('demod', [status(thm)], ['98', '99'])).
% 30.57/30.80  thf('101', plain,
% 30.57/30.80      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 30.57/30.80        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 30.57/30.80            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['95', '100'])).
% 30.57/30.80  thf('102', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 30.57/30.80  thf('103', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 30.57/30.80  thf('104', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['102', '103'])).
% 30.57/30.80  thf('105', plain,
% 30.57/30.80      (![X3 : $i]:
% 30.57/30.80         (~ (v2_funct_1 @ X3)
% 30.57/30.80          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 30.57/30.80              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 30.57/30.80          | ~ (v1_funct_1 @ X3)
% 30.57/30.80          | ~ (v1_relat_1 @ X3))),
% 30.57/30.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 30.57/30.80  thf('106', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(d1_funct_2, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i]:
% 30.57/30.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.57/30.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.57/30.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 30.57/30.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 30.57/30.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.57/30.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 30.57/30.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 30.57/30.80  thf(zf_stmt_1, axiom,
% 30.57/30.80    (![C:$i,B:$i,A:$i]:
% 30.57/30.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 30.57/30.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 30.57/30.80  thf('107', plain,
% 30.57/30.80      (![X22 : $i, X23 : $i, X24 : $i]:
% 30.57/30.80         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 30.57/30.80          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 30.57/30.80          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.57/30.80  thf('108', plain,
% 30.57/30.80      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 30.57/30.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 30.57/30.80      inference('sup-', [status(thm)], ['106', '107'])).
% 30.57/30.80  thf('109', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 30.57/30.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 30.57/30.80  thf(zf_stmt_4, axiom,
% 30.57/30.80    (![B:$i,A:$i]:
% 30.57/30.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.57/30.80       ( zip_tseitin_0 @ B @ A ) ))).
% 30.57/30.80  thf(zf_stmt_5, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i]:
% 30.57/30.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.57/30.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 30.57/30.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.57/30.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 30.57/30.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 30.57/30.80  thf('110', plain,
% 30.57/30.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 30.57/30.80         (~ (zip_tseitin_0 @ X25 @ X26)
% 30.57/30.80          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 30.57/30.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.57/30.80  thf('111', plain,
% 30.57/30.80      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 30.57/30.80      inference('sup-', [status(thm)], ['109', '110'])).
% 30.57/30.80  thf('112', plain,
% 30.57/30.80      (![X20 : $i, X21 : $i]:
% 30.57/30.80         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.57/30.80  thf('113', plain,
% 30.57/30.80      (![X20 : $i, X21 : $i]:
% 30.57/30.80         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.57/30.80  thf('114', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 30.57/30.80      inference('simplify', [status(thm)], ['113'])).
% 30.57/30.80  thf('115', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.57/30.80         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 30.57/30.80      inference('sup+', [status(thm)], ['112', '114'])).
% 30.57/30.80  thf('116', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 30.57/30.80      inference('eq_fact', [status(thm)], ['115'])).
% 30.57/30.80  thf('117', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 30.57/30.80      inference('demod', [status(thm)], ['111', '116'])).
% 30.57/30.80  thf('118', plain,
% 30.57/30.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf(redefinition_k1_relset_1, axiom,
% 30.57/30.80    (![A:$i,B:$i,C:$i]:
% 30.57/30.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.57/30.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 30.57/30.80  thf('119', plain,
% 30.57/30.80      (![X10 : $i, X11 : $i, X12 : $i]:
% 30.57/30.80         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 30.57/30.80          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 30.57/30.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.57/30.80  thf('120', plain,
% 30.57/30.80      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 30.57/30.80      inference('sup-', [status(thm)], ['118', '119'])).
% 30.57/30.80  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['108', '117', '120'])).
% 30.57/30.80  thf('122', plain,
% 30.57/30.80      (![X3 : $i]:
% 30.57/30.80         (~ (v2_funct_1 @ X3)
% 30.57/30.80          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 30.57/30.80              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 30.57/30.80          | ~ (v1_funct_1 @ X3)
% 30.57/30.80          | ~ (v1_relat_1 @ X3))),
% 30.57/30.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 30.57/30.80  thf('123', plain,
% 30.57/30.80      (![X33 : $i]:
% 30.57/30.80         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 30.57/30.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 30.57/30.80      inference('demod', [status(thm)], ['52', '53'])).
% 30.57/30.80  thf('124', plain,
% 30.57/30.80      (![X0 : $i]:
% 30.57/30.80         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 30.57/30.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 30.57/30.80          | ~ (v1_relat_1 @ X0)
% 30.57/30.80          | ~ (v1_funct_1 @ X0)
% 30.57/30.80          | ~ (v2_funct_1 @ X0))),
% 30.57/30.80      inference('sup+', [status(thm)], ['122', '123'])).
% 30.57/30.80  thf('125', plain,
% 30.57/30.80      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 30.57/30.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 30.57/30.80        | ~ (v2_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v1_relat_1 @ sk_B))),
% 30.57/30.80      inference('sup+', [status(thm)], ['121', '124'])).
% 30.57/30.80  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['108', '117', '120'])).
% 30.57/30.80  thf('127', plain, ((v2_funct_1 @ sk_B)),
% 30.57/30.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 30.57/30.80  thf('128', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('129', plain, ((v1_relat_1 @ sk_B)),
% 30.57/30.80      inference('sup-', [status(thm)], ['44', '45'])).
% 30.57/30.80  thf('130', plain,
% 30.57/30.80      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 30.57/30.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.57/30.80      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 30.57/30.80  thf('131', plain,
% 30.57/30.80      (![X0 : $i, X1 : $i]:
% 30.57/30.80         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 30.57/30.80          | ((k6_relat_1 @ X0) = (X1))
% 30.57/30.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['67', '68'])).
% 30.57/30.80  thf('132', plain,
% 30.57/30.80      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 30.57/30.80        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 30.57/30.80             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['130', '131'])).
% 30.57/30.80  thf('133', plain,
% 30.57/30.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 30.57/30.80           (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 30.57/30.80        | ~ (v1_relat_1 @ sk_B)
% 30.57/30.80        | ~ (v1_funct_1 @ sk_B)
% 30.57/30.80        | ~ (v2_funct_1 @ sk_B)
% 30.57/30.80        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 30.57/30.80      inference('sup-', [status(thm)], ['105', '132'])).
% 30.57/30.80  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 30.57/30.80      inference('demod', [status(thm)], ['108', '117', '120'])).
% 30.57/30.80  thf('135', plain,
% 30.57/30.80      (![X0 : $i]:
% 30.57/30.80         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 30.57/30.80      inference('sup-', [status(thm)], ['73', '75'])).
% 30.57/30.80  thf('136', plain, ((v1_relat_1 @ sk_B)),
% 30.57/30.80      inference('sup-', [status(thm)], ['44', '45'])).
% 30.57/30.80  thf('137', plain, ((v1_funct_1 @ sk_B)),
% 30.57/30.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.57/30.80  thf('138', plain, ((v2_funct_1 @ sk_B)),
% 30.57/30.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 30.57/30.80  thf('139', plain,
% 30.57/30.80      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 30.57/30.80      inference('demod', [status(thm)],
% 30.57/30.80                ['133', '134', '135', '136', '137', '138'])).
% 30.57/30.80  thf('140', plain,
% 30.57/30.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 30.57/30.80         = (k6_relat_1 @ sk_A))),
% 30.57/30.80      inference('demod', [status(thm)], ['101', '104', '139'])).
% 30.57/30.80  thf('141', plain,
% 30.57/30.80      (![X0 : $i]:
% 30.57/30.80         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 30.57/30.80      inference('sup-', [status(thm)], ['73', '75'])).
% 30.57/30.80  thf('142', plain, ($false),
% 30.57/30.80      inference('demod', [status(thm)], ['92', '140', '141'])).
% 30.57/30.80  
% 30.57/30.80  % SZS output end Refutation
% 30.57/30.80  
% 30.57/30.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
