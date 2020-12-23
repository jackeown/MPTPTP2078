%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bOQYSuYUfB

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:21 EST 2020

% Result     : Theorem 7.29s
% Output     : Refutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 604 expanded)
%              Number of leaves         :   47 ( 203 expanded)
%              Depth                    :   17
%              Number of atoms          : 1829 (11976 expanded)
%              Number of equality atoms :   71 ( 158 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( ( k2_funct_2 @ X42 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) )
      | ~ ( v3_funct_2 @ X41 @ X42 @ X42 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X42 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_2 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('54',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
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
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('112',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('113',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','113'])).

thf('115',plain,(
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

thf('116',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('117',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('119',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('120',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['118','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['121'])).

thf('123',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['117','122'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['114','123'])).

thf('125',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('126',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['114','123'])).

thf('130',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('131',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('133',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('135',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','135'])).

thf('137',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['114','123'])).

thf('138',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('139',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('140',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('142',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141'])).

thf('143',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['103','106','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['94','143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bOQYSuYUfB
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.29/7.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.29/7.50  % Solved by: fo/fo7.sh
% 7.29/7.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.29/7.50  % done 4338 iterations in 7.033s
% 7.29/7.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.29/7.50  % SZS output start Refutation
% 7.29/7.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.29/7.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 7.29/7.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.29/7.50  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 7.29/7.50  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 7.29/7.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.29/7.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.29/7.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.29/7.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 7.29/7.50  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 7.29/7.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.29/7.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.29/7.50  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 7.29/7.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 7.29/7.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 7.29/7.50  thf(sk_B_type, type, sk_B: $i).
% 7.29/7.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.29/7.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 7.29/7.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.29/7.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.29/7.50  thf(sk_A_type, type, sk_A: $i).
% 7.29/7.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.29/7.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 7.29/7.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.29/7.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 7.29/7.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.29/7.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.29/7.50  thf(t88_funct_2, conjecture,
% 7.29/7.50    (![A:$i,B:$i]:
% 7.29/7.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.29/7.50         ( v3_funct_2 @ B @ A @ A ) & 
% 7.29/7.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.29/7.50       ( ( r2_relset_1 @
% 7.29/7.50           A @ A @ 
% 7.29/7.50           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 7.29/7.50           ( k6_partfun1 @ A ) ) & 
% 7.29/7.50         ( r2_relset_1 @
% 7.29/7.50           A @ A @ 
% 7.29/7.50           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 7.29/7.50           ( k6_partfun1 @ A ) ) ) ))).
% 7.29/7.50  thf(zf_stmt_0, negated_conjecture,
% 7.29/7.50    (~( ![A:$i,B:$i]:
% 7.29/7.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.29/7.50            ( v3_funct_2 @ B @ A @ A ) & 
% 7.29/7.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.29/7.50          ( ( r2_relset_1 @
% 7.29/7.50              A @ A @ 
% 7.29/7.50              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 7.29/7.50              ( k6_partfun1 @ A ) ) & 
% 7.29/7.50            ( r2_relset_1 @
% 7.29/7.50              A @ A @ 
% 7.29/7.50              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 7.29/7.50              ( k6_partfun1 @ A ) ) ) ) )),
% 7.29/7.50    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 7.29/7.50  thf('0', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50           (k6_partfun1 @ sk_A))
% 7.29/7.50        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50             (k6_partfun1 @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('1', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50           (k6_partfun1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('split', [status(esa)], ['0'])).
% 7.29/7.50  thf(redefinition_k6_partfun1, axiom,
% 7.29/7.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 7.29/7.50  thf('2', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.29/7.50  thf('3', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50           (k6_relat_1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('demod', [status(thm)], ['1', '2'])).
% 7.29/7.50  thf('4', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(redefinition_k2_funct_2, axiom,
% 7.29/7.50    (![A:$i,B:$i]:
% 7.29/7.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.29/7.50         ( v3_funct_2 @ B @ A @ A ) & 
% 7.29/7.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.29/7.50       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 7.29/7.50  thf('5', plain,
% 7.29/7.50      (![X41 : $i, X42 : $i]:
% 7.29/7.50         (((k2_funct_2 @ X42 @ X41) = (k2_funct_1 @ X41))
% 7.29/7.50          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))
% 7.29/7.50          | ~ (v3_funct_2 @ X41 @ X42 @ X42)
% 7.29/7.50          | ~ (v1_funct_2 @ X41 @ X42 @ X42)
% 7.29/7.50          | ~ (v1_funct_1 @ X41))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 7.29/7.50  thf('6', plain,
% 7.29/7.50      ((~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['4', '5'])).
% 7.29/7.50  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 7.29/7.50  thf('11', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50            (k2_funct_1 @ sk_B)) @ 
% 7.29/7.50           (k6_relat_1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('demod', [status(thm)], ['3', '10'])).
% 7.29/7.50  thf('12', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('13', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(dt_k2_funct_2, axiom,
% 7.29/7.50    (![A:$i,B:$i]:
% 7.29/7.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 7.29/7.50         ( v3_funct_2 @ B @ A @ A ) & 
% 7.29/7.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 7.29/7.50       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 7.29/7.50         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 7.29/7.50         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 7.29/7.50         ( m1_subset_1 @
% 7.29/7.50           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 7.29/7.50  thf('14', plain,
% 7.29/7.50      (![X31 : $i, X32 : $i]:
% 7.29/7.50         ((m1_subset_1 @ (k2_funct_2 @ X31 @ X32) @ 
% 7.29/7.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 7.29/7.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 7.29/7.50          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 7.29/7.50          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 7.29/7.50          | ~ (v1_funct_1 @ X32))),
% 7.29/7.50      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 7.29/7.50  thf('15', plain,
% 7.29/7.50      ((~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.29/7.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['13', '14'])).
% 7.29/7.50  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('19', plain,
% 7.29/7.50      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.29/7.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 7.29/7.50  thf(redefinition_k1_partfun1, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.29/7.50     ( ( ( v1_funct_1 @ E ) & 
% 7.29/7.50         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.29/7.50         ( v1_funct_1 @ F ) & 
% 7.29/7.50         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 7.29/7.50       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 7.29/7.50  thf('20', plain,
% 7.29/7.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.29/7.50         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 7.29/7.50          | ~ (v1_funct_1 @ X35)
% 7.29/7.50          | ~ (v1_funct_1 @ X38)
% 7.29/7.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.29/7.50          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 7.29/7.50              = (k5_relat_1 @ X35 @ X38)))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 7.29/7.50  thf('21', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.29/7.50         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.29/7.50            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 7.29/7.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.29/7.50          | ~ (v1_funct_1 @ X0)
% 7.29/7.50          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['19', '20'])).
% 7.29/7.50  thf('22', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('23', plain,
% 7.29/7.50      (![X31 : $i, X32 : $i]:
% 7.29/7.50         ((v1_funct_1 @ (k2_funct_2 @ X31 @ X32))
% 7.29/7.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 7.29/7.50          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 7.29/7.50          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 7.29/7.50          | ~ (v1_funct_1 @ X32))),
% 7.29/7.50      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 7.29/7.50  thf('24', plain,
% 7.29/7.50      ((~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['22', '23'])).
% 7.29/7.50  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('26', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('28', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 7.29/7.50  thf('29', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.29/7.50         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.29/7.50            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 7.29/7.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.29/7.50          | ~ (v1_funct_1 @ X0))),
% 7.29/7.50      inference('demod', [status(thm)], ['21', '28'])).
% 7.29/7.50  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 7.29/7.50  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 7.29/7.50  thf('32', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.29/7.50         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 7.29/7.50            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 7.29/7.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.29/7.50          | ~ (v1_funct_1 @ X0))),
% 7.29/7.50      inference('demod', [status(thm)], ['29', '30', '31'])).
% 7.29/7.50  thf('33', plain,
% 7.29/7.50      ((~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 7.29/7.50            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['12', '32'])).
% 7.29/7.50  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(t61_funct_1, axiom,
% 7.29/7.50    (![A:$i]:
% 7.29/7.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.29/7.50       ( ( v2_funct_1 @ A ) =>
% 7.29/7.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 7.29/7.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 7.29/7.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 7.29/7.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 7.29/7.50  thf('35', plain,
% 7.29/7.50      (![X7 : $i]:
% 7.29/7.50         (~ (v2_funct_1 @ X7)
% 7.29/7.50          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 7.29/7.50              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 7.29/7.50          | ~ (v1_funct_1 @ X7)
% 7.29/7.50          | ~ (v1_relat_1 @ X7))),
% 7.29/7.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 7.29/7.50  thf('36', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(cc2_funct_2, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i]:
% 7.29/7.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.29/7.50       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 7.29/7.50         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 7.29/7.50  thf('37', plain,
% 7.29/7.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.29/7.50         (~ (v1_funct_1 @ X18)
% 7.29/7.50          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 7.29/7.50          | (v2_funct_2 @ X18 @ X20)
% 7.29/7.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 7.29/7.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 7.29/7.50  thf('38', plain,
% 7.29/7.50      (((v2_funct_2 @ sk_B @ sk_A)
% 7.29/7.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ~ (v1_funct_1 @ sk_B))),
% 7.29/7.50      inference('sup-', [status(thm)], ['36', '37'])).
% 7.29/7.50  thf('39', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('41', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 7.29/7.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 7.29/7.50  thf(d3_funct_2, axiom,
% 7.29/7.50    (![A:$i,B:$i]:
% 7.29/7.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 7.29/7.50       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 7.29/7.50  thf('42', plain,
% 7.29/7.50      (![X29 : $i, X30 : $i]:
% 7.29/7.50         (~ (v2_funct_2 @ X30 @ X29)
% 7.29/7.50          | ((k2_relat_1 @ X30) = (X29))
% 7.29/7.50          | ~ (v5_relat_1 @ X30 @ X29)
% 7.29/7.50          | ~ (v1_relat_1 @ X30))),
% 7.29/7.50      inference('cnf', [status(esa)], [d3_funct_2])).
% 7.29/7.50  thf('43', plain,
% 7.29/7.50      ((~ (v1_relat_1 @ sk_B)
% 7.29/7.50        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 7.29/7.50        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['41', '42'])).
% 7.29/7.50  thf('44', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(cc2_relat_1, axiom,
% 7.29/7.50    (![A:$i]:
% 7.29/7.50     ( ( v1_relat_1 @ A ) =>
% 7.29/7.50       ( ![B:$i]:
% 7.29/7.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 7.29/7.50  thf('45', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i]:
% 7.29/7.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 7.29/7.50          | (v1_relat_1 @ X0)
% 7.29/7.50          | ~ (v1_relat_1 @ X1))),
% 7.29/7.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.29/7.50  thf('46', plain,
% 7.29/7.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 7.29/7.50      inference('sup-', [status(thm)], ['44', '45'])).
% 7.29/7.50  thf(fc6_relat_1, axiom,
% 7.29/7.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 7.29/7.50  thf('47', plain,
% 7.29/7.50      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 7.29/7.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.29/7.50  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['46', '47'])).
% 7.29/7.50  thf('49', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(cc2_relset_1, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i]:
% 7.29/7.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.29/7.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.29/7.50  thf('50', plain,
% 7.29/7.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.29/7.50         ((v5_relat_1 @ X8 @ X10)
% 7.29/7.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 7.29/7.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.29/7.50  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 7.29/7.50      inference('sup-', [status(thm)], ['49', '50'])).
% 7.29/7.50  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 7.29/7.50      inference('demod', [status(thm)], ['43', '48', '51'])).
% 7.29/7.50  thf('53', plain,
% 7.29/7.50      (![X7 : $i]:
% 7.29/7.50         (~ (v2_funct_1 @ X7)
% 7.29/7.50          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 7.29/7.50              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 7.29/7.50          | ~ (v1_funct_1 @ X7)
% 7.29/7.50          | ~ (v1_relat_1 @ X7))),
% 7.29/7.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 7.29/7.50  thf(dt_k6_partfun1, axiom,
% 7.29/7.50    (![A:$i]:
% 7.29/7.50     ( ( m1_subset_1 @
% 7.29/7.50         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 7.29/7.50       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 7.29/7.50  thf('54', plain,
% 7.29/7.50      (![X34 : $i]:
% 7.29/7.50         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 7.29/7.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 7.29/7.50      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 7.29/7.50  thf('55', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.29/7.50  thf('56', plain,
% 7.29/7.50      (![X34 : $i]:
% 7.29/7.50         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 7.29/7.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 7.29/7.50      inference('demod', [status(thm)], ['54', '55'])).
% 7.29/7.50  thf('57', plain,
% 7.29/7.50      (![X0 : $i]:
% 7.29/7.50         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 7.29/7.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 7.29/7.50          | ~ (v1_relat_1 @ X0)
% 7.29/7.50          | ~ (v1_funct_1 @ X0)
% 7.29/7.50          | ~ (v2_funct_1 @ X0))),
% 7.29/7.50      inference('sup+', [status(thm)], ['53', '56'])).
% 7.29/7.50  thf('58', plain,
% 7.29/7.50      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 7.29/7.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 7.29/7.50        | ~ (v2_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_relat_1 @ sk_B))),
% 7.29/7.50      inference('sup+', [status(thm)], ['52', '57'])).
% 7.29/7.50  thf('59', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 7.29/7.50      inference('demod', [status(thm)], ['43', '48', '51'])).
% 7.29/7.50  thf('60', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('61', plain,
% 7.29/7.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.29/7.50         (~ (v1_funct_1 @ X18)
% 7.29/7.50          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 7.29/7.50          | (v2_funct_1 @ X18)
% 7.29/7.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 7.29/7.50      inference('cnf', [status(esa)], [cc2_funct_2])).
% 7.29/7.50  thf('62', plain,
% 7.29/7.50      (((v2_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ~ (v1_funct_1 @ sk_B))),
% 7.29/7.50      inference('sup-', [status(thm)], ['60', '61'])).
% 7.29/7.50  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['62', '63', '64'])).
% 7.29/7.50  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['46', '47'])).
% 7.29/7.50  thf('68', plain,
% 7.29/7.50      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 7.29/7.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('demod', [status(thm)], ['58', '59', '65', '66', '67'])).
% 7.29/7.50  thf('69', plain,
% 7.29/7.50      (![X34 : $i]:
% 7.29/7.50         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 7.29/7.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 7.29/7.50      inference('demod', [status(thm)], ['54', '55'])).
% 7.29/7.50  thf(redefinition_r2_relset_1, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i,D:$i]:
% 7.29/7.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.29/7.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.29/7.50       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 7.29/7.50  thf('70', plain,
% 7.29/7.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 7.29/7.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 7.29/7.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 7.29/7.50          | ((X14) = (X17))
% 7.29/7.50          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 7.29/7.50  thf('71', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i]:
% 7.29/7.50         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 7.29/7.50          | ((k6_relat_1 @ X0) = (X1))
% 7.29/7.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['69', '70'])).
% 7.29/7.50  thf('72', plain,
% 7.29/7.50      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 7.29/7.50        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 7.29/7.50             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['68', '71'])).
% 7.29/7.50  thf('73', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 7.29/7.50           (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 7.29/7.50        | ~ (v1_relat_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v2_funct_1 @ sk_B)
% 7.29/7.50        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['35', '72'])).
% 7.29/7.50  thf('74', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 7.29/7.50      inference('demod', [status(thm)], ['43', '48', '51'])).
% 7.29/7.50  thf('75', plain,
% 7.29/7.50      (![X34 : $i]:
% 7.29/7.50         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 7.29/7.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 7.29/7.50      inference('demod', [status(thm)], ['54', '55'])).
% 7.29/7.50  thf('76', plain,
% 7.29/7.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 7.29/7.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 7.29/7.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 7.29/7.50          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 7.29/7.50          | ((X14) != (X17)))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 7.29/7.50  thf('77', plain,
% 7.29/7.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.29/7.50         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 7.29/7.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 7.29/7.50      inference('simplify', [status(thm)], ['76'])).
% 7.29/7.50  thf('78', plain,
% 7.29/7.50      (![X0 : $i]:
% 7.29/7.50         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 7.29/7.50      inference('sup-', [status(thm)], ['75', '77'])).
% 7.29/7.50  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['46', '47'])).
% 7.29/7.50  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['62', '63', '64'])).
% 7.29/7.50  thf('82', plain,
% 7.29/7.50      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['73', '74', '78', '79', '80', '81'])).
% 7.29/7.50  thf('83', plain,
% 7.29/7.50      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 7.29/7.50         = (k6_relat_1 @ sk_A))),
% 7.29/7.50      inference('demod', [status(thm)], ['33', '34', '82'])).
% 7.29/7.50  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 7.29/7.50  thf('85', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50           (k6_partfun1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('split', [status(esa)], ['0'])).
% 7.29/7.50  thf('86', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.29/7.50  thf('87', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50           (k6_relat_1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('demod', [status(thm)], ['85', '86'])).
% 7.29/7.50  thf('88', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 7.29/7.50            sk_B) @ 
% 7.29/7.50           (k6_relat_1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['84', '87'])).
% 7.29/7.50  thf('89', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 7.29/7.50           (k6_relat_1 @ sk_A)))
% 7.29/7.50         <= (~
% 7.29/7.50             ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50               (k6_partfun1 @ sk_A))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['83', '88'])).
% 7.29/7.50  thf('90', plain,
% 7.29/7.50      (![X0 : $i]:
% 7.29/7.50         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 7.29/7.50      inference('sup-', [status(thm)], ['75', '77'])).
% 7.29/7.50  thf('91', plain,
% 7.29/7.50      (((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50         (k6_partfun1 @ sk_A)))),
% 7.29/7.50      inference('demod', [status(thm)], ['89', '90'])).
% 7.29/7.50  thf('92', plain,
% 7.29/7.50      (~
% 7.29/7.50       ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50         (k6_partfun1 @ sk_A))) | 
% 7.29/7.50       ~
% 7.29/7.50       ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 7.29/7.50          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 7.29/7.50         (k6_partfun1 @ sk_A)))),
% 7.29/7.50      inference('split', [status(esa)], ['0'])).
% 7.29/7.50  thf('93', plain,
% 7.29/7.50      (~
% 7.29/7.50       ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 7.29/7.50         (k6_partfun1 @ sk_A)))),
% 7.29/7.50      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 7.29/7.50  thf('94', plain,
% 7.29/7.50      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 7.29/7.50          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 7.29/7.50          (k6_relat_1 @ sk_A))),
% 7.29/7.50      inference('simpl_trail', [status(thm)], ['11', '93'])).
% 7.29/7.50  thf('95', plain,
% 7.29/7.50      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 7.29/7.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 7.29/7.50  thf('96', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 7.29/7.50  thf('97', plain,
% 7.29/7.50      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 7.29/7.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('demod', [status(thm)], ['95', '96'])).
% 7.29/7.50  thf('98', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('99', plain,
% 7.29/7.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.29/7.50         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 7.29/7.50          | ~ (v1_funct_1 @ X35)
% 7.29/7.50          | ~ (v1_funct_1 @ X38)
% 7.29/7.50          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.29/7.50          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 7.29/7.50              = (k5_relat_1 @ X35 @ X38)))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 7.29/7.50  thf('100', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.29/7.50         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 7.29/7.50            = (k5_relat_1 @ sk_B @ X0))
% 7.29/7.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.29/7.50          | ~ (v1_funct_1 @ X0)
% 7.29/7.50          | ~ (v1_funct_1 @ sk_B))),
% 7.29/7.50      inference('sup-', [status(thm)], ['98', '99'])).
% 7.29/7.50  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('102', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.29/7.50         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 7.29/7.50            = (k5_relat_1 @ sk_B @ X0))
% 7.29/7.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.29/7.50          | ~ (v1_funct_1 @ X0))),
% 7.29/7.50      inference('demod', [status(thm)], ['100', '101'])).
% 7.29/7.50  thf('103', plain,
% 7.29/7.50      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 7.29/7.50        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 7.29/7.50            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['97', '102'])).
% 7.29/7.50  thf('104', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 7.29/7.50  thf('105', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 7.29/7.50  thf('106', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['104', '105'])).
% 7.29/7.50  thf('107', plain,
% 7.29/7.50      (![X7 : $i]:
% 7.29/7.50         (~ (v2_funct_1 @ X7)
% 7.29/7.50          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 7.29/7.50              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 7.29/7.50          | ~ (v1_funct_1 @ X7)
% 7.29/7.50          | ~ (v1_relat_1 @ X7))),
% 7.29/7.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 7.29/7.50  thf('108', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(d1_funct_2, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i]:
% 7.29/7.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.29/7.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.29/7.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.29/7.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.29/7.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.29/7.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.29/7.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.29/7.50  thf(zf_stmt_1, axiom,
% 7.29/7.50    (![C:$i,B:$i,A:$i]:
% 7.29/7.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.29/7.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.29/7.50  thf('109', plain,
% 7.29/7.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.29/7.50         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 7.29/7.50          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 7.29/7.50          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.29/7.50  thf('110', plain,
% 7.29/7.50      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 7.29/7.50        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 7.29/7.50      inference('sup-', [status(thm)], ['108', '109'])).
% 7.29/7.50  thf('111', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(redefinition_k1_relset_1, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i]:
% 7.29/7.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.29/7.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.29/7.50  thf('112', plain,
% 7.29/7.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 7.29/7.50         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 7.29/7.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 7.29/7.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.29/7.50  thf('113', plain,
% 7.29/7.50      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 7.29/7.50      inference('sup-', [status(thm)], ['111', '112'])).
% 7.29/7.50  thf('114', plain,
% 7.29/7.50      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_B)))),
% 7.29/7.50      inference('demod', [status(thm)], ['110', '113'])).
% 7.29/7.50  thf('115', plain,
% 7.29/7.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.29/7.50  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 7.29/7.50  thf(zf_stmt_4, axiom,
% 7.29/7.50    (![B:$i,A:$i]:
% 7.29/7.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.29/7.50       ( zip_tseitin_0 @ B @ A ) ))).
% 7.29/7.50  thf(zf_stmt_5, axiom,
% 7.29/7.50    (![A:$i,B:$i,C:$i]:
% 7.29/7.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.29/7.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.29/7.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.29/7.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.29/7.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.29/7.50  thf('116', plain,
% 7.29/7.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.29/7.50         (~ (zip_tseitin_0 @ X26 @ X27)
% 7.29/7.50          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 7.29/7.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.29/7.50  thf('117', plain,
% 7.29/7.50      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 7.29/7.50      inference('sup-', [status(thm)], ['115', '116'])).
% 7.29/7.50  thf('118', plain,
% 7.29/7.50      (![X21 : $i, X22 : $i]:
% 7.29/7.50         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 7.29/7.50  thf('119', plain,
% 7.29/7.50      (![X21 : $i, X22 : $i]:
% 7.29/7.50         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 7.29/7.50  thf('120', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 7.29/7.50      inference('simplify', [status(thm)], ['119'])).
% 7.29/7.50  thf('121', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.29/7.50         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 7.29/7.50      inference('sup+', [status(thm)], ['118', '120'])).
% 7.29/7.50  thf('122', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 7.29/7.50      inference('eq_fact', [status(thm)], ['121'])).
% 7.29/7.50  thf('123', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 7.29/7.50      inference('demod', [status(thm)], ['117', '122'])).
% 7.29/7.50  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['114', '123'])).
% 7.29/7.50  thf('125', plain,
% 7.29/7.50      (![X7 : $i]:
% 7.29/7.50         (~ (v2_funct_1 @ X7)
% 7.29/7.50          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 7.29/7.50              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 7.29/7.50          | ~ (v1_funct_1 @ X7)
% 7.29/7.50          | ~ (v1_relat_1 @ X7))),
% 7.29/7.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 7.29/7.50  thf('126', plain,
% 7.29/7.50      (![X34 : $i]:
% 7.29/7.50         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 7.29/7.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 7.29/7.50      inference('demod', [status(thm)], ['54', '55'])).
% 7.29/7.50  thf('127', plain,
% 7.29/7.50      (![X0 : $i]:
% 7.29/7.50         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 7.29/7.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 7.29/7.50          | ~ (v1_relat_1 @ X0)
% 7.29/7.50          | ~ (v1_funct_1 @ X0)
% 7.29/7.50          | ~ (v2_funct_1 @ X0))),
% 7.29/7.50      inference('sup+', [status(thm)], ['125', '126'])).
% 7.29/7.50  thf('128', plain,
% 7.29/7.50      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 7.29/7.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 7.29/7.50        | ~ (v2_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v1_relat_1 @ sk_B))),
% 7.29/7.50      inference('sup+', [status(thm)], ['124', '127'])).
% 7.29/7.50  thf('129', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['114', '123'])).
% 7.29/7.50  thf('130', plain, ((v2_funct_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['62', '63', '64'])).
% 7.29/7.50  thf('131', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('132', plain, ((v1_relat_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['46', '47'])).
% 7.29/7.50  thf('133', plain,
% 7.29/7.50      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 7.29/7.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.29/7.50      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 7.29/7.50  thf('134', plain,
% 7.29/7.50      (![X0 : $i, X1 : $i]:
% 7.29/7.50         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 7.29/7.50          | ((k6_relat_1 @ X0) = (X1))
% 7.29/7.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['69', '70'])).
% 7.29/7.50  thf('135', plain,
% 7.29/7.50      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 7.29/7.50        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 7.29/7.50             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['133', '134'])).
% 7.29/7.50  thf('136', plain,
% 7.29/7.50      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 7.29/7.50           (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 7.29/7.50        | ~ (v1_relat_1 @ sk_B)
% 7.29/7.50        | ~ (v1_funct_1 @ sk_B)
% 7.29/7.50        | ~ (v2_funct_1 @ sk_B)
% 7.29/7.50        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 7.29/7.50      inference('sup-', [status(thm)], ['107', '135'])).
% 7.29/7.50  thf('137', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 7.29/7.50      inference('demod', [status(thm)], ['114', '123'])).
% 7.29/7.50  thf('138', plain,
% 7.29/7.50      (![X0 : $i]:
% 7.29/7.50         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 7.29/7.50      inference('sup-', [status(thm)], ['75', '77'])).
% 7.29/7.50  thf('139', plain, ((v1_relat_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['46', '47'])).
% 7.29/7.50  thf('140', plain, ((v1_funct_1 @ sk_B)),
% 7.29/7.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.29/7.50  thf('141', plain, ((v2_funct_1 @ sk_B)),
% 7.29/7.50      inference('demod', [status(thm)], ['62', '63', '64'])).
% 7.29/7.50  thf('142', plain,
% 7.29/7.50      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 7.29/7.50      inference('demod', [status(thm)],
% 7.29/7.50                ['136', '137', '138', '139', '140', '141'])).
% 7.29/7.50  thf('143', plain,
% 7.29/7.50      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 7.29/7.50         = (k6_relat_1 @ sk_A))),
% 7.29/7.50      inference('demod', [status(thm)], ['103', '106', '142'])).
% 7.29/7.50  thf('144', plain,
% 7.29/7.50      (![X0 : $i]:
% 7.29/7.50         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 7.29/7.50      inference('sup-', [status(thm)], ['75', '77'])).
% 7.29/7.50  thf('145', plain, ($false),
% 7.29/7.50      inference('demod', [status(thm)], ['94', '143', '144'])).
% 7.29/7.50  
% 7.29/7.50  % SZS output end Refutation
% 7.29/7.50  
% 7.29/7.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
