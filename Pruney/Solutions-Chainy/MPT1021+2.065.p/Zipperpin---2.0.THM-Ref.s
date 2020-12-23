%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.migQCjd01O

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:21 EST 2020

% Result     : Theorem 25.14s
% Output     : Refutation 25.14s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 601 expanded)
%              Number of leaves         :   47 ( 203 expanded)
%              Depth                    :   17
%              Number of atoms          : 1821 (11952 expanded)
%              Number of equality atoms :   70 ( 155 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( ( k2_funct_2 @ X44 @ X43 )
        = ( k2_funct_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) )
      | ~ ( v3_funct_2 @ X43 @ X44 @ X44 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_2 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_2 @ X32 @ X31 )
      | ( ( k2_relat_1 @ X32 )
        = X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('54',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('75',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('82',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','78','79','80','81'])).

thf('83',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','82'])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('96',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
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
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('105',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('108',plain,(
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

thf('109',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
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

thf('112',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('113',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['117'])).

thf('119',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['113','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('121',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('122',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['110','119','122'])).

thf('124',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('125',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['110','119','122'])).

thf('129',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('130',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('132',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('134',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','134'])).

thf('136',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['110','119','122'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('138',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('139',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('141',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140'])).

thf('142',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','106','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['94','142','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.migQCjd01O
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:10:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 25.14/25.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 25.14/25.37  % Solved by: fo/fo7.sh
% 25.14/25.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.14/25.37  % done 6595 iterations in 24.915s
% 25.14/25.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 25.14/25.37  % SZS output start Refutation
% 25.14/25.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 25.14/25.37  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 25.14/25.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 25.14/25.37  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 25.14/25.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 25.14/25.37  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 25.14/25.37  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 25.14/25.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 25.14/25.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 25.14/25.37  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 25.14/25.37  thf(sk_A_type, type, sk_A: $i).
% 25.14/25.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 25.14/25.37  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 25.14/25.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 25.14/25.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 25.14/25.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 25.14/25.38  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 25.14/25.38  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 25.14/25.38  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 25.14/25.38  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 25.14/25.38  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 25.14/25.38  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 25.14/25.38  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 25.14/25.38  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 25.14/25.38  thf(sk_B_type, type, sk_B: $i).
% 25.14/25.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 25.14/25.38  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 25.14/25.38  thf(t88_funct_2, conjecture,
% 25.14/25.38    (![A:$i,B:$i]:
% 25.14/25.38     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 25.14/25.38         ( v3_funct_2 @ B @ A @ A ) & 
% 25.14/25.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 25.14/25.38       ( ( r2_relset_1 @
% 25.14/25.38           A @ A @ 
% 25.14/25.38           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 25.14/25.38           ( k6_partfun1 @ A ) ) & 
% 25.14/25.38         ( r2_relset_1 @
% 25.14/25.38           A @ A @ 
% 25.14/25.38           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 25.14/25.38           ( k6_partfun1 @ A ) ) ) ))).
% 25.14/25.38  thf(zf_stmt_0, negated_conjecture,
% 25.14/25.38    (~( ![A:$i,B:$i]:
% 25.14/25.38        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 25.14/25.38            ( v3_funct_2 @ B @ A @ A ) & 
% 25.14/25.38            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 25.14/25.38          ( ( r2_relset_1 @
% 25.14/25.38              A @ A @ 
% 25.14/25.38              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 25.14/25.38              ( k6_partfun1 @ A ) ) & 
% 25.14/25.38            ( r2_relset_1 @
% 25.14/25.38              A @ A @ 
% 25.14/25.38              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 25.14/25.38              ( k6_partfun1 @ A ) ) ) ) )),
% 25.14/25.38    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 25.14/25.38  thf('0', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38           (k6_partfun1 @ sk_A))
% 25.14/25.38        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38             (k6_partfun1 @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('1', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38           (k6_partfun1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('split', [status(esa)], ['0'])).
% 25.14/25.38  thf(redefinition_k6_partfun1, axiom,
% 25.14/25.38    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 25.14/25.38  thf('2', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 25.14/25.38  thf('3', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38           (k6_relat_1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('demod', [status(thm)], ['1', '2'])).
% 25.14/25.38  thf('4', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(redefinition_k2_funct_2, axiom,
% 25.14/25.38    (![A:$i,B:$i]:
% 25.14/25.38     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 25.14/25.38         ( v3_funct_2 @ B @ A @ A ) & 
% 25.14/25.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 25.14/25.38       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 25.14/25.38  thf('5', plain,
% 25.14/25.38      (![X43 : $i, X44 : $i]:
% 25.14/25.38         (((k2_funct_2 @ X44 @ X43) = (k2_funct_1 @ X43))
% 25.14/25.38          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))
% 25.14/25.38          | ~ (v3_funct_2 @ X43 @ X44 @ X44)
% 25.14/25.38          | ~ (v1_funct_2 @ X43 @ X44 @ X44)
% 25.14/25.38          | ~ (v1_funct_1 @ X43))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 25.14/25.38  thf('6', plain,
% 25.14/25.38      ((~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['4', '5'])).
% 25.14/25.38  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 25.14/25.38  thf('11', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38            (k2_funct_1 @ sk_B)) @ 
% 25.14/25.38           (k6_relat_1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('demod', [status(thm)], ['3', '10'])).
% 25.14/25.38  thf('12', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('13', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(dt_k2_funct_2, axiom,
% 25.14/25.38    (![A:$i,B:$i]:
% 25.14/25.38     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 25.14/25.38         ( v3_funct_2 @ B @ A @ A ) & 
% 25.14/25.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 25.14/25.38       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 25.14/25.38         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 25.14/25.38         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 25.14/25.38         ( m1_subset_1 @
% 25.14/25.38           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 25.14/25.38  thf('14', plain,
% 25.14/25.38      (![X33 : $i, X34 : $i]:
% 25.14/25.38         ((m1_subset_1 @ (k2_funct_2 @ X33 @ X34) @ 
% 25.14/25.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 25.14/25.38          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 25.14/25.38          | ~ (v3_funct_2 @ X34 @ X33 @ X33)
% 25.14/25.38          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 25.14/25.38          | ~ (v1_funct_1 @ X34))),
% 25.14/25.38      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 25.14/25.38  thf('15', plain,
% 25.14/25.38      ((~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 25.14/25.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['13', '14'])).
% 25.14/25.38  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('19', plain,
% 25.14/25.38      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 25.14/25.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 25.14/25.38  thf(redefinition_k1_partfun1, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 25.14/25.38     ( ( ( v1_funct_1 @ E ) & 
% 25.14/25.38         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 25.14/25.38         ( v1_funct_1 @ F ) & 
% 25.14/25.38         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 25.14/25.38       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 25.14/25.38  thf('20', plain,
% 25.14/25.38      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 25.14/25.38         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 25.14/25.38          | ~ (v1_funct_1 @ X37)
% 25.14/25.38          | ~ (v1_funct_1 @ X40)
% 25.14/25.38          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 25.14/25.38          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 25.14/25.38              = (k5_relat_1 @ X37 @ X40)))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 25.14/25.38  thf('21', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.14/25.38         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 25.14/25.38            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 25.14/25.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 25.14/25.38          | ~ (v1_funct_1 @ X0)
% 25.14/25.38          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['19', '20'])).
% 25.14/25.38  thf('22', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('23', plain,
% 25.14/25.38      (![X33 : $i, X34 : $i]:
% 25.14/25.38         ((v1_funct_1 @ (k2_funct_2 @ X33 @ X34))
% 25.14/25.38          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 25.14/25.38          | ~ (v3_funct_2 @ X34 @ X33 @ X33)
% 25.14/25.38          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 25.14/25.38          | ~ (v1_funct_1 @ X34))),
% 25.14/25.38      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 25.14/25.38  thf('24', plain,
% 25.14/25.38      ((~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['22', '23'])).
% 25.14/25.38  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('26', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('28', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 25.14/25.38  thf('29', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.14/25.38         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 25.14/25.38            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 25.14/25.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 25.14/25.38          | ~ (v1_funct_1 @ X0))),
% 25.14/25.38      inference('demod', [status(thm)], ['21', '28'])).
% 25.14/25.38  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 25.14/25.38  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 25.14/25.38  thf('32', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.14/25.38         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 25.14/25.38            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 25.14/25.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 25.14/25.38          | ~ (v1_funct_1 @ X0))),
% 25.14/25.38      inference('demod', [status(thm)], ['29', '30', '31'])).
% 25.14/25.38  thf('33', plain,
% 25.14/25.38      ((~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 25.14/25.38            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['12', '32'])).
% 25.14/25.38  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(t61_funct_1, axiom,
% 25.14/25.38    (![A:$i]:
% 25.14/25.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 25.14/25.38       ( ( v2_funct_1 @ A ) =>
% 25.14/25.38         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 25.14/25.38             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 25.14/25.38           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 25.14/25.38             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 25.14/25.38  thf('35', plain,
% 25.14/25.38      (![X9 : $i]:
% 25.14/25.38         (~ (v2_funct_1 @ X9)
% 25.14/25.38          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 25.14/25.38              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 25.14/25.38          | ~ (v1_funct_1 @ X9)
% 25.14/25.38          | ~ (v1_relat_1 @ X9))),
% 25.14/25.38      inference('cnf', [status(esa)], [t61_funct_1])).
% 25.14/25.38  thf('36', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(cc2_funct_2, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i]:
% 25.14/25.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.14/25.38       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 25.14/25.38         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 25.14/25.38  thf('37', plain,
% 25.14/25.38      (![X20 : $i, X21 : $i, X22 : $i]:
% 25.14/25.38         (~ (v1_funct_1 @ X20)
% 25.14/25.38          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 25.14/25.38          | (v2_funct_2 @ X20 @ X22)
% 25.14/25.38          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 25.14/25.38      inference('cnf', [status(esa)], [cc2_funct_2])).
% 25.14/25.38  thf('38', plain,
% 25.14/25.38      (((v2_funct_2 @ sk_B @ sk_A)
% 25.14/25.38        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ~ (v1_funct_1 @ sk_B))),
% 25.14/25.38      inference('sup-', [status(thm)], ['36', '37'])).
% 25.14/25.38  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 25.14/25.38      inference('demod', [status(thm)], ['38', '39', '40'])).
% 25.14/25.38  thf(d3_funct_2, axiom,
% 25.14/25.38    (![A:$i,B:$i]:
% 25.14/25.38     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 25.14/25.38       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 25.14/25.38  thf('42', plain,
% 25.14/25.38      (![X31 : $i, X32 : $i]:
% 25.14/25.38         (~ (v2_funct_2 @ X32 @ X31)
% 25.14/25.38          | ((k2_relat_1 @ X32) = (X31))
% 25.14/25.38          | ~ (v5_relat_1 @ X32 @ X31)
% 25.14/25.38          | ~ (v1_relat_1 @ X32))),
% 25.14/25.38      inference('cnf', [status(esa)], [d3_funct_2])).
% 25.14/25.38  thf('43', plain,
% 25.14/25.38      ((~ (v1_relat_1 @ sk_B)
% 25.14/25.38        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 25.14/25.38        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['41', '42'])).
% 25.14/25.38  thf('44', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(cc2_relat_1, axiom,
% 25.14/25.38    (![A:$i]:
% 25.14/25.38     ( ( v1_relat_1 @ A ) =>
% 25.14/25.38       ( ![B:$i]:
% 25.14/25.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 25.14/25.38  thf('45', plain,
% 25.14/25.38      (![X4 : $i, X5 : $i]:
% 25.14/25.38         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 25.14/25.38          | (v1_relat_1 @ X4)
% 25.14/25.38          | ~ (v1_relat_1 @ X5))),
% 25.14/25.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 25.14/25.38  thf('46', plain,
% 25.14/25.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 25.14/25.38      inference('sup-', [status(thm)], ['44', '45'])).
% 25.14/25.38  thf(fc6_relat_1, axiom,
% 25.14/25.38    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 25.14/25.38  thf('47', plain,
% 25.14/25.38      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 25.14/25.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 25.14/25.38  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['46', '47'])).
% 25.14/25.38  thf('49', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(cc2_relset_1, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i]:
% 25.14/25.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.14/25.38       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 25.14/25.38  thf('50', plain,
% 25.14/25.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 25.14/25.38         ((v5_relat_1 @ X10 @ X12)
% 25.14/25.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 25.14/25.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 25.14/25.38  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 25.14/25.38      inference('sup-', [status(thm)], ['49', '50'])).
% 25.14/25.38  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 25.14/25.38      inference('demod', [status(thm)], ['43', '48', '51'])).
% 25.14/25.38  thf('53', plain,
% 25.14/25.38      (![X9 : $i]:
% 25.14/25.38         (~ (v2_funct_1 @ X9)
% 25.14/25.38          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 25.14/25.38              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 25.14/25.38          | ~ (v1_funct_1 @ X9)
% 25.14/25.38          | ~ (v1_relat_1 @ X9))),
% 25.14/25.38      inference('cnf', [status(esa)], [t61_funct_1])).
% 25.14/25.38  thf(dt_k6_partfun1, axiom,
% 25.14/25.38    (![A:$i]:
% 25.14/25.38     ( ( m1_subset_1 @
% 25.14/25.38         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 25.14/25.38       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 25.14/25.38  thf('54', plain,
% 25.14/25.38      (![X36 : $i]:
% 25.14/25.38         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 25.14/25.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 25.14/25.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 25.14/25.38  thf('55', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 25.14/25.38  thf('56', plain,
% 25.14/25.38      (![X36 : $i]:
% 25.14/25.38         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 25.14/25.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 25.14/25.38      inference('demod', [status(thm)], ['54', '55'])).
% 25.14/25.38  thf('57', plain,
% 25.14/25.38      (![X0 : $i]:
% 25.14/25.38         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 25.14/25.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 25.14/25.38          | ~ (v1_relat_1 @ X0)
% 25.14/25.38          | ~ (v1_funct_1 @ X0)
% 25.14/25.38          | ~ (v2_funct_1 @ X0))),
% 25.14/25.38      inference('sup+', [status(thm)], ['53', '56'])).
% 25.14/25.38  thf('58', plain,
% 25.14/25.38      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 25.14/25.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 25.14/25.38        | ~ (v2_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_relat_1 @ sk_B))),
% 25.14/25.38      inference('sup+', [status(thm)], ['52', '57'])).
% 25.14/25.38  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 25.14/25.38      inference('demod', [status(thm)], ['43', '48', '51'])).
% 25.14/25.38  thf('60', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('61', plain,
% 25.14/25.38      (![X20 : $i, X21 : $i, X22 : $i]:
% 25.14/25.38         (~ (v1_funct_1 @ X20)
% 25.14/25.38          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 25.14/25.38          | (v2_funct_1 @ X20)
% 25.14/25.38          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 25.14/25.38      inference('cnf', [status(esa)], [cc2_funct_2])).
% 25.14/25.38  thf('62', plain,
% 25.14/25.38      (((v2_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ~ (v1_funct_1 @ sk_B))),
% 25.14/25.38      inference('sup-', [status(thm)], ['60', '61'])).
% 25.14/25.38  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['62', '63', '64'])).
% 25.14/25.38  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['46', '47'])).
% 25.14/25.38  thf('68', plain,
% 25.14/25.38      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 25.14/25.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 25.14/25.38  thf('69', plain,
% 25.14/25.38      (![X36 : $i]:
% 25.14/25.38         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 25.14/25.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 25.14/25.38      inference('demod', [status(thm)], ['54', '55'])).
% 25.14/25.38  thf(redefinition_r2_relset_1, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i,D:$i]:
% 25.14/25.38     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 25.14/25.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.14/25.38       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 25.14/25.38  thf('70', plain,
% 25.14/25.38      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 25.14/25.38         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 25.14/25.38          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 25.14/25.38          | ((X16) = (X19))
% 25.14/25.38          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 25.14/25.38  thf('71', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i]:
% 25.14/25.38         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 25.14/25.38          | ((k6_relat_1 @ X0) = (X1))
% 25.14/25.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['69', '70'])).
% 25.14/25.38  thf('72', plain,
% 25.14/25.38      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 25.14/25.38        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 25.14/25.38             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['68', '71'])).
% 25.14/25.38  thf('73', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 25.14/25.38           (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 25.14/25.38        | ~ (v1_relat_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v2_funct_1 @ sk_B)
% 25.14/25.38        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['35', '72'])).
% 25.14/25.38  thf('74', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 25.14/25.38      inference('demod', [status(thm)], ['43', '48', '51'])).
% 25.14/25.38  thf('75', plain,
% 25.14/25.38      (![X36 : $i]:
% 25.14/25.38         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 25.14/25.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 25.14/25.38      inference('demod', [status(thm)], ['54', '55'])).
% 25.14/25.38  thf('76', plain,
% 25.14/25.38      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 25.14/25.38         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 25.14/25.38          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 25.14/25.38          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 25.14/25.38          | ((X16) != (X19)))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 25.14/25.38  thf('77', plain,
% 25.14/25.38      (![X17 : $i, X18 : $i, X19 : $i]:
% 25.14/25.38         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 25.14/25.38          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 25.14/25.38      inference('simplify', [status(thm)], ['76'])).
% 25.14/25.38  thf('78', plain,
% 25.14/25.38      (![X0 : $i]:
% 25.14/25.38         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 25.14/25.38      inference('sup-', [status(thm)], ['75', '77'])).
% 25.14/25.38  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['46', '47'])).
% 25.14/25.38  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['62', '63', '64'])).
% 25.14/25.38  thf('82', plain,
% 25.14/25.38      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['73', '74', '78', '79', '80', '81'])).
% 25.14/25.38  thf('83', plain,
% 25.14/25.38      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 25.14/25.38         = (k6_relat_1 @ sk_A))),
% 25.14/25.38      inference('demod', [status(thm)], ['33', '34', '82'])).
% 25.14/25.38  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 25.14/25.38  thf('85', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38           (k6_partfun1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('split', [status(esa)], ['0'])).
% 25.14/25.38  thf('86', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 25.14/25.38  thf('87', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38           (k6_relat_1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('demod', [status(thm)], ['85', '86'])).
% 25.14/25.38  thf('88', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 25.14/25.38            sk_B) @ 
% 25.14/25.38           (k6_relat_1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['84', '87'])).
% 25.14/25.38  thf('89', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 25.14/25.38           (k6_relat_1 @ sk_A)))
% 25.14/25.38         <= (~
% 25.14/25.38             ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38               (k6_partfun1 @ sk_A))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['83', '88'])).
% 25.14/25.38  thf('90', plain,
% 25.14/25.38      (![X0 : $i]:
% 25.14/25.38         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 25.14/25.38      inference('sup-', [status(thm)], ['75', '77'])).
% 25.14/25.38  thf('91', plain,
% 25.14/25.38      (((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38         (k6_partfun1 @ sk_A)))),
% 25.14/25.38      inference('demod', [status(thm)], ['89', '90'])).
% 25.14/25.38  thf('92', plain,
% 25.14/25.38      (~
% 25.14/25.38       ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38         (k6_partfun1 @ sk_A))) | 
% 25.14/25.38       ~
% 25.14/25.38       ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 25.14/25.38          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 25.14/25.38         (k6_partfun1 @ sk_A)))),
% 25.14/25.38      inference('split', [status(esa)], ['0'])).
% 25.14/25.38  thf('93', plain,
% 25.14/25.38      (~
% 25.14/25.38       ((r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 25.14/25.38         (k6_partfun1 @ sk_A)))),
% 25.14/25.38      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 25.14/25.38  thf('94', plain,
% 25.14/25.38      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 25.14/25.38          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 25.14/25.38          (k6_relat_1 @ sk_A))),
% 25.14/25.38      inference('simpl_trail', [status(thm)], ['11', '93'])).
% 25.14/25.38  thf('95', plain,
% 25.14/25.38      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 25.14/25.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 25.14/25.38  thf('96', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 25.14/25.38  thf('97', plain,
% 25.14/25.38      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 25.14/25.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('demod', [status(thm)], ['95', '96'])).
% 25.14/25.38  thf('98', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('99', plain,
% 25.14/25.38      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 25.14/25.38         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 25.14/25.38          | ~ (v1_funct_1 @ X37)
% 25.14/25.38          | ~ (v1_funct_1 @ X40)
% 25.14/25.38          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 25.14/25.38          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 25.14/25.38              = (k5_relat_1 @ X37 @ X40)))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 25.14/25.38  thf('100', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.14/25.38         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 25.14/25.38            = (k5_relat_1 @ sk_B @ X0))
% 25.14/25.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 25.14/25.38          | ~ (v1_funct_1 @ X0)
% 25.14/25.38          | ~ (v1_funct_1 @ sk_B))),
% 25.14/25.38      inference('sup-', [status(thm)], ['98', '99'])).
% 25.14/25.38  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('102', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.14/25.38         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 25.14/25.38            = (k5_relat_1 @ sk_B @ X0))
% 25.14/25.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 25.14/25.38          | ~ (v1_funct_1 @ X0))),
% 25.14/25.38      inference('demod', [status(thm)], ['100', '101'])).
% 25.14/25.38  thf('103', plain,
% 25.14/25.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 25.14/25.38        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 25.14/25.38            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['97', '102'])).
% 25.14/25.38  thf('104', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 25.14/25.38  thf('105', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 25.14/25.38  thf('106', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['104', '105'])).
% 25.14/25.38  thf('107', plain,
% 25.14/25.38      (![X9 : $i]:
% 25.14/25.38         (~ (v2_funct_1 @ X9)
% 25.14/25.38          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 25.14/25.38              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 25.14/25.38          | ~ (v1_funct_1 @ X9)
% 25.14/25.38          | ~ (v1_relat_1 @ X9))),
% 25.14/25.38      inference('cnf', [status(esa)], [t61_funct_1])).
% 25.14/25.38  thf('108', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(d1_funct_2, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i]:
% 25.14/25.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.14/25.38       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 25.14/25.38           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 25.14/25.38             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 25.14/25.38         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 25.14/25.38           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 25.14/25.38             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 25.14/25.38  thf(zf_stmt_1, axiom,
% 25.14/25.38    (![C:$i,B:$i,A:$i]:
% 25.14/25.38     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 25.14/25.38       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 25.14/25.38  thf('109', plain,
% 25.14/25.38      (![X25 : $i, X26 : $i, X27 : $i]:
% 25.14/25.38         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 25.14/25.38          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 25.14/25.38          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.14/25.38  thf('110', plain,
% 25.14/25.38      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 25.14/25.38        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 25.14/25.38      inference('sup-', [status(thm)], ['108', '109'])).
% 25.14/25.38  thf('111', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 25.14/25.38  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 25.14/25.38  thf(zf_stmt_4, axiom,
% 25.14/25.38    (![B:$i,A:$i]:
% 25.14/25.38     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 25.14/25.38       ( zip_tseitin_0 @ B @ A ) ))).
% 25.14/25.38  thf(zf_stmt_5, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i]:
% 25.14/25.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.14/25.38       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 25.14/25.38         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 25.14/25.38           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 25.14/25.38             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 25.14/25.38  thf('112', plain,
% 25.14/25.38      (![X28 : $i, X29 : $i, X30 : $i]:
% 25.14/25.38         (~ (zip_tseitin_0 @ X28 @ X29)
% 25.14/25.38          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 25.14/25.38          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.14/25.38  thf('113', plain,
% 25.14/25.38      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 25.14/25.38      inference('sup-', [status(thm)], ['111', '112'])).
% 25.14/25.38  thf('114', plain,
% 25.14/25.38      (![X23 : $i, X24 : $i]:
% 25.14/25.38         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.14/25.38  thf('115', plain,
% 25.14/25.38      (![X23 : $i, X24 : $i]:
% 25.14/25.38         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_4])).
% 25.14/25.38  thf('116', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 25.14/25.38      inference('simplify', [status(thm)], ['115'])).
% 25.14/25.38  thf('117', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.14/25.38         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 25.14/25.38      inference('sup+', [status(thm)], ['114', '116'])).
% 25.14/25.38  thf('118', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 25.14/25.38      inference('eq_fact', [status(thm)], ['117'])).
% 25.14/25.38  thf('119', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 25.14/25.38      inference('demod', [status(thm)], ['113', '118'])).
% 25.14/25.38  thf('120', plain,
% 25.14/25.38      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf(redefinition_k1_relset_1, axiom,
% 25.14/25.38    (![A:$i,B:$i,C:$i]:
% 25.14/25.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.14/25.38       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 25.14/25.38  thf('121', plain,
% 25.14/25.38      (![X13 : $i, X14 : $i, X15 : $i]:
% 25.14/25.38         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 25.14/25.38          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 25.14/25.38      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.14/25.38  thf('122', plain,
% 25.14/25.38      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 25.14/25.38      inference('sup-', [status(thm)], ['120', '121'])).
% 25.14/25.38  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['110', '119', '122'])).
% 25.14/25.38  thf('124', plain,
% 25.14/25.38      (![X9 : $i]:
% 25.14/25.38         (~ (v2_funct_1 @ X9)
% 25.14/25.38          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 25.14/25.38              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 25.14/25.38          | ~ (v1_funct_1 @ X9)
% 25.14/25.38          | ~ (v1_relat_1 @ X9))),
% 25.14/25.38      inference('cnf', [status(esa)], [t61_funct_1])).
% 25.14/25.38  thf('125', plain,
% 25.14/25.38      (![X36 : $i]:
% 25.14/25.38         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 25.14/25.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 25.14/25.38      inference('demod', [status(thm)], ['54', '55'])).
% 25.14/25.38  thf('126', plain,
% 25.14/25.38      (![X0 : $i]:
% 25.14/25.38         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 25.14/25.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 25.14/25.38          | ~ (v1_relat_1 @ X0)
% 25.14/25.38          | ~ (v1_funct_1 @ X0)
% 25.14/25.38          | ~ (v2_funct_1 @ X0))),
% 25.14/25.38      inference('sup+', [status(thm)], ['124', '125'])).
% 25.14/25.38  thf('127', plain,
% 25.14/25.38      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 25.14/25.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 25.14/25.38        | ~ (v2_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v1_relat_1 @ sk_B))),
% 25.14/25.38      inference('sup+', [status(thm)], ['123', '126'])).
% 25.14/25.38  thf('128', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['110', '119', '122'])).
% 25.14/25.38  thf('129', plain, ((v2_funct_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['62', '63', '64'])).
% 25.14/25.38  thf('130', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('131', plain, ((v1_relat_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['46', '47'])).
% 25.14/25.38  thf('132', plain,
% 25.14/25.38      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 25.14/25.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 25.14/25.38      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 25.14/25.38  thf('133', plain,
% 25.14/25.38      (![X0 : $i, X1 : $i]:
% 25.14/25.38         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 25.14/25.38          | ((k6_relat_1 @ X0) = (X1))
% 25.14/25.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['69', '70'])).
% 25.14/25.38  thf('134', plain,
% 25.14/25.38      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 25.14/25.38        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 25.14/25.38             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['132', '133'])).
% 25.14/25.38  thf('135', plain,
% 25.14/25.38      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 25.14/25.38           (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 25.14/25.38        | ~ (v1_relat_1 @ sk_B)
% 25.14/25.38        | ~ (v1_funct_1 @ sk_B)
% 25.14/25.38        | ~ (v2_funct_1 @ sk_B)
% 25.14/25.38        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 25.14/25.38      inference('sup-', [status(thm)], ['107', '134'])).
% 25.14/25.38  thf('136', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 25.14/25.38      inference('demod', [status(thm)], ['110', '119', '122'])).
% 25.14/25.38  thf('137', plain,
% 25.14/25.38      (![X0 : $i]:
% 25.14/25.38         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 25.14/25.38      inference('sup-', [status(thm)], ['75', '77'])).
% 25.14/25.38  thf('138', plain, ((v1_relat_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['46', '47'])).
% 25.14/25.38  thf('139', plain, ((v1_funct_1 @ sk_B)),
% 25.14/25.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.14/25.38  thf('140', plain, ((v2_funct_1 @ sk_B)),
% 25.14/25.38      inference('demod', [status(thm)], ['62', '63', '64'])).
% 25.14/25.38  thf('141', plain,
% 25.14/25.38      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 25.14/25.38      inference('demod', [status(thm)],
% 25.14/25.38                ['135', '136', '137', '138', '139', '140'])).
% 25.14/25.38  thf('142', plain,
% 25.14/25.38      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 25.14/25.38         = (k6_relat_1 @ sk_A))),
% 25.14/25.38      inference('demod', [status(thm)], ['103', '106', '141'])).
% 25.14/25.38  thf('143', plain,
% 25.14/25.38      (![X0 : $i]:
% 25.14/25.38         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 25.14/25.38      inference('sup-', [status(thm)], ['75', '77'])).
% 25.14/25.38  thf('144', plain, ($false),
% 25.14/25.38      inference('demod', [status(thm)], ['94', '142', '143'])).
% 25.14/25.38  
% 25.14/25.38  % SZS output end Refutation
% 25.14/25.38  
% 25.14/25.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
