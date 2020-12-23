%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hqIod8Lyk2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:13 EST 2020

% Result     : Theorem 31.41s
% Output     : Refutation 31.41s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 476 expanded)
%              Number of leaves         :   46 ( 164 expanded)
%              Depth                    :   19
%              Number of atoms          : 1688 (10123 expanded)
%              Number of equality atoms :   63 ( 106 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X7 @ ( k2_funct_1 @ X7 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( ( k2_funct_2 @ X45 @ X44 )
        = ( k2_funct_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) )
      | ~ ( v3_funct_2 @ X44 @ X45 @ X45 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('32',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

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

thf('36',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('54',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('61',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('67',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','64','65','66'])).

thf('68',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('69',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('74',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('75',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('81',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','77','78','79','80'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','81'])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('84',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('85',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('90',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('104',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('105',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','106'])).

thf('108',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','107'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
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

thf('113',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('117',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('120',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['114','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('122',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('123',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('126',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('127',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['108','124','125','126','127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hqIod8Lyk2
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 31.41/31.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.41/31.63  % Solved by: fo/fo7.sh
% 31.41/31.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.41/31.63  % done 9177 iterations in 31.184s
% 31.41/31.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.41/31.63  % SZS output start Refutation
% 31.41/31.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 31.41/31.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 31.41/31.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 31.41/31.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 31.41/31.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.41/31.63  thf(sk_B_type, type, sk_B: $i).
% 31.41/31.63  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 31.41/31.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 31.41/31.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.41/31.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 31.41/31.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 31.41/31.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 31.41/31.63  thf(sk_A_type, type, sk_A: $i).
% 31.41/31.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 31.41/31.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 31.41/31.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 31.41/31.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.41/31.63  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 31.41/31.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 31.41/31.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 31.41/31.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 31.41/31.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 31.41/31.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 31.41/31.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 31.41/31.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 31.41/31.63  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 31.41/31.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 31.41/31.63  thf(t61_funct_1, axiom,
% 31.41/31.63    (![A:$i]:
% 31.41/31.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 31.41/31.63       ( ( v2_funct_1 @ A ) =>
% 31.41/31.63         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 31.41/31.63             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 31.41/31.63           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 31.41/31.63             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 31.41/31.63  thf('0', plain,
% 31.41/31.63      (![X7 : $i]:
% 31.41/31.63         (~ (v2_funct_1 @ X7)
% 31.41/31.63          | ((k5_relat_1 @ X7 @ (k2_funct_1 @ X7))
% 31.41/31.63              = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 31.41/31.63          | ~ (v1_funct_1 @ X7)
% 31.41/31.63          | ~ (v1_relat_1 @ X7))),
% 31.41/31.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 31.41/31.63  thf(t88_funct_2, conjecture,
% 31.41/31.63    (![A:$i,B:$i]:
% 31.41/31.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 31.41/31.63         ( v3_funct_2 @ B @ A @ A ) & 
% 31.41/31.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 31.41/31.63       ( ( r2_relset_1 @
% 31.41/31.63           A @ A @ 
% 31.41/31.63           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 31.41/31.63           ( k6_partfun1 @ A ) ) & 
% 31.41/31.63         ( r2_relset_1 @
% 31.41/31.63           A @ A @ 
% 31.41/31.63           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 31.41/31.63           ( k6_partfun1 @ A ) ) ) ))).
% 31.41/31.63  thf(zf_stmt_0, negated_conjecture,
% 31.41/31.63    (~( ![A:$i,B:$i]:
% 31.41/31.63        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 31.41/31.63            ( v3_funct_2 @ B @ A @ A ) & 
% 31.41/31.63            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 31.41/31.63          ( ( r2_relset_1 @
% 31.41/31.63              A @ A @ 
% 31.41/31.63              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 31.41/31.63              ( k6_partfun1 @ A ) ) & 
% 31.41/31.63            ( r2_relset_1 @
% 31.41/31.63              A @ A @ 
% 31.41/31.63              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 31.41/31.63              ( k6_partfun1 @ A ) ) ) ) )),
% 31.41/31.63    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 31.41/31.63  thf('1', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63           (k6_partfun1 @ sk_A))
% 31.41/31.63        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63             (k6_partfun1 @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('2', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63           (k6_partfun1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('split', [status(esa)], ['1'])).
% 31.41/31.63  thf(redefinition_k6_partfun1, axiom,
% 31.41/31.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 31.41/31.63  thf('3', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 31.41/31.63  thf('4', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63           (k6_relat_1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('demod', [status(thm)], ['2', '3'])).
% 31.41/31.63  thf('5', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(redefinition_k2_funct_2, axiom,
% 31.41/31.63    (![A:$i,B:$i]:
% 31.41/31.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 31.41/31.63         ( v3_funct_2 @ B @ A @ A ) & 
% 31.41/31.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 31.41/31.63       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 31.41/31.63  thf('6', plain,
% 31.41/31.63      (![X44 : $i, X45 : $i]:
% 31.41/31.63         (((k2_funct_2 @ X45 @ X44) = (k2_funct_1 @ X44))
% 31.41/31.63          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))
% 31.41/31.63          | ~ (v3_funct_2 @ X44 @ X45 @ X45)
% 31.41/31.63          | ~ (v1_funct_2 @ X44 @ X45 @ X45)
% 31.41/31.63          | ~ (v1_funct_1 @ X44))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 31.41/31.63  thf('7', plain,
% 31.41/31.63      ((~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['5', '6'])).
% 31.41/31.63  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 31.41/31.63  thf('12', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63            (k2_funct_1 @ sk_B)) @ 
% 31.41/31.63           (k6_relat_1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('demod', [status(thm)], ['4', '11'])).
% 31.41/31.63  thf('13', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('14', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(dt_k2_funct_2, axiom,
% 31.41/31.63    (![A:$i,B:$i]:
% 31.41/31.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 31.41/31.63         ( v3_funct_2 @ B @ A @ A ) & 
% 31.41/31.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 31.41/31.63       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 31.41/31.63         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 31.41/31.63         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 31.41/31.63         ( m1_subset_1 @
% 31.41/31.63           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 31.41/31.63  thf('15', plain,
% 31.41/31.63      (![X34 : $i, X35 : $i]:
% 31.41/31.63         ((m1_subset_1 @ (k2_funct_2 @ X34 @ X35) @ 
% 31.41/31.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 31.41/31.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 31.41/31.63          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 31.41/31.63          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 31.41/31.63          | ~ (v1_funct_1 @ X35))),
% 31.41/31.63      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 31.41/31.63  thf('16', plain,
% 31.41/31.63      ((~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 31.41/31.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 31.41/31.63      inference('sup-', [status(thm)], ['14', '15'])).
% 31.41/31.63  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('19', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('20', plain,
% 31.41/31.63      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 31.41/31.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 31.41/31.63  thf(redefinition_k1_partfun1, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 31.41/31.63     ( ( ( v1_funct_1 @ E ) & 
% 31.41/31.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 31.41/31.63         ( v1_funct_1 @ F ) & 
% 31.41/31.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 31.41/31.63       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 31.41/31.63  thf('21', plain,
% 31.41/31.63      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 31.41/31.63         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 31.41/31.63          | ~ (v1_funct_1 @ X38)
% 31.41/31.63          | ~ (v1_funct_1 @ X41)
% 31.41/31.63          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 31.41/31.63          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 31.41/31.63              = (k5_relat_1 @ X38 @ X41)))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 31.41/31.63  thf('22', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.41/31.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 31.41/31.63            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 31.41/31.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 31.41/31.63          | ~ (v1_funct_1 @ X0)
% 31.41/31.63          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['20', '21'])).
% 31.41/31.63  thf('23', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('24', plain,
% 31.41/31.63      (![X34 : $i, X35 : $i]:
% 31.41/31.63         ((v1_funct_1 @ (k2_funct_2 @ X34 @ X35))
% 31.41/31.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 31.41/31.63          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 31.41/31.63          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 31.41/31.63          | ~ (v1_funct_1 @ X35))),
% 31.41/31.63      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 31.41/31.63  thf('25', plain,
% 31.41/31.63      ((~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['23', '24'])).
% 31.41/31.63  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 31.41/31.63  thf('30', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.41/31.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 31.41/31.63            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 31.41/31.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 31.41/31.63          | ~ (v1_funct_1 @ X0))),
% 31.41/31.63      inference('demod', [status(thm)], ['22', '29'])).
% 31.41/31.63  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 31.41/31.63  thf('32', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 31.41/31.63  thf('33', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.41/31.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 31.41/31.63            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 31.41/31.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 31.41/31.63          | ~ (v1_funct_1 @ X0))),
% 31.41/31.63      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.41/31.63  thf('34', plain,
% 31.41/31.63      ((~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 31.41/31.63            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['13', '33'])).
% 31.41/31.63  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('36', plain,
% 31.41/31.63      (![X7 : $i]:
% 31.41/31.63         (~ (v2_funct_1 @ X7)
% 31.41/31.63          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 31.41/31.63              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 31.41/31.63          | ~ (v1_funct_1 @ X7)
% 31.41/31.63          | ~ (v1_relat_1 @ X7))),
% 31.41/31.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 31.41/31.63  thf('37', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(cc2_funct_2, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i]:
% 31.41/31.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.41/31.63       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 31.41/31.63         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 31.41/31.63  thf('38', plain,
% 31.41/31.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 31.41/31.63         (~ (v1_funct_1 @ X21)
% 31.41/31.63          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 31.41/31.63          | (v2_funct_2 @ X21 @ X23)
% 31.41/31.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 31.41/31.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 31.41/31.63  thf('39', plain,
% 31.41/31.63      (((v2_funct_2 @ sk_B @ sk_A)
% 31.41/31.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ~ (v1_funct_1 @ sk_B))),
% 31.41/31.63      inference('sup-', [status(thm)], ['37', '38'])).
% 31.41/31.63  thf('40', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('42', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 31.41/31.63      inference('demod', [status(thm)], ['39', '40', '41'])).
% 31.41/31.63  thf(d3_funct_2, axiom,
% 31.41/31.63    (![A:$i,B:$i]:
% 31.41/31.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 31.41/31.63       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 31.41/31.63  thf('43', plain,
% 31.41/31.63      (![X32 : $i, X33 : $i]:
% 31.41/31.63         (~ (v2_funct_2 @ X33 @ X32)
% 31.41/31.63          | ((k2_relat_1 @ X33) = (X32))
% 31.41/31.63          | ~ (v5_relat_1 @ X33 @ X32)
% 31.41/31.63          | ~ (v1_relat_1 @ X33))),
% 31.41/31.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 31.41/31.63  thf('44', plain,
% 31.41/31.63      ((~ (v1_relat_1 @ sk_B)
% 31.41/31.63        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 31.41/31.63        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['42', '43'])).
% 31.41/31.63  thf('45', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(cc1_relset_1, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i]:
% 31.41/31.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.41/31.63       ( v1_relat_1 @ C ) ))).
% 31.41/31.63  thf('46', plain,
% 31.41/31.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 31.41/31.63         ((v1_relat_1 @ X8)
% 31.41/31.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 31.41/31.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 31.41/31.63  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 31.41/31.63      inference('sup-', [status(thm)], ['45', '46'])).
% 31.41/31.63  thf('48', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(cc2_relset_1, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i]:
% 31.41/31.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.41/31.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 31.41/31.63  thf('49', plain,
% 31.41/31.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 31.41/31.63         ((v5_relat_1 @ X11 @ X13)
% 31.41/31.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 31.41/31.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 31.41/31.63  thf('50', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 31.41/31.63      inference('sup-', [status(thm)], ['48', '49'])).
% 31.41/31.63  thf('51', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 31.41/31.63      inference('demod', [status(thm)], ['44', '47', '50'])).
% 31.41/31.63  thf('52', plain,
% 31.41/31.63      (![X7 : $i]:
% 31.41/31.63         (~ (v2_funct_1 @ X7)
% 31.41/31.63          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 31.41/31.63              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 31.41/31.63          | ~ (v1_funct_1 @ X7)
% 31.41/31.63          | ~ (v1_relat_1 @ X7))),
% 31.41/31.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 31.41/31.63  thf(dt_k6_partfun1, axiom,
% 31.41/31.63    (![A:$i]:
% 31.41/31.63     ( ( m1_subset_1 @
% 31.41/31.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 31.41/31.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 31.41/31.63  thf('53', plain,
% 31.41/31.63      (![X37 : $i]:
% 31.41/31.63         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 31.41/31.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 31.41/31.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 31.41/31.63  thf('54', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 31.41/31.63  thf('55', plain,
% 31.41/31.63      (![X37 : $i]:
% 31.41/31.63         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 31.41/31.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 31.41/31.63      inference('demod', [status(thm)], ['53', '54'])).
% 31.41/31.63  thf('56', plain,
% 31.41/31.63      (![X0 : $i]:
% 31.41/31.63         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 31.41/31.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 31.41/31.63          | ~ (v1_relat_1 @ X0)
% 31.41/31.63          | ~ (v1_funct_1 @ X0)
% 31.41/31.63          | ~ (v2_funct_1 @ X0))),
% 31.41/31.63      inference('sup+', [status(thm)], ['52', '55'])).
% 31.41/31.63  thf('57', plain,
% 31.41/31.63      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 31.41/31.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 31.41/31.63        | ~ (v2_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v1_relat_1 @ sk_B))),
% 31.41/31.63      inference('sup+', [status(thm)], ['51', '56'])).
% 31.41/31.63  thf('58', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 31.41/31.63      inference('demod', [status(thm)], ['44', '47', '50'])).
% 31.41/31.63  thf('59', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('60', plain,
% 31.41/31.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 31.41/31.63         (~ (v1_funct_1 @ X21)
% 31.41/31.63          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 31.41/31.63          | (v2_funct_1 @ X21)
% 31.41/31.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 31.41/31.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 31.41/31.63  thf('61', plain,
% 31.41/31.63      (((v2_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ~ (v1_funct_1 @ sk_B))),
% 31.41/31.63      inference('sup-', [status(thm)], ['59', '60'])).
% 31.41/31.63  thf('62', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('64', plain, ((v2_funct_1 @ sk_B)),
% 31.41/31.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 31.41/31.63  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 31.41/31.63      inference('sup-', [status(thm)], ['45', '46'])).
% 31.41/31.63  thf('67', plain,
% 31.41/31.63      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 31.41/31.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('demod', [status(thm)], ['57', '58', '64', '65', '66'])).
% 31.41/31.63  thf('68', plain,
% 31.41/31.63      (![X37 : $i]:
% 31.41/31.63         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 31.41/31.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 31.41/31.63      inference('demod', [status(thm)], ['53', '54'])).
% 31.41/31.63  thf(redefinition_r2_relset_1, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i,D:$i]:
% 31.41/31.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 31.41/31.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 31.41/31.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 31.41/31.63  thf('69', plain,
% 31.41/31.63      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 31.41/31.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 31.41/31.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 31.41/31.63          | ((X17) = (X20))
% 31.41/31.63          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 31.41/31.63  thf('70', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i]:
% 31.41/31.63         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 31.41/31.63          | ((k6_relat_1 @ X0) = (X1))
% 31.41/31.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 31.41/31.63      inference('sup-', [status(thm)], ['68', '69'])).
% 31.41/31.63  thf('71', plain,
% 31.41/31.63      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 31.41/31.63        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 31.41/31.63             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['67', '70'])).
% 31.41/31.63  thf('72', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 31.41/31.63           (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 31.41/31.63        | ~ (v1_relat_1 @ sk_B)
% 31.41/31.63        | ~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v2_funct_1 @ sk_B)
% 31.41/31.63        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['36', '71'])).
% 31.41/31.63  thf('73', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 31.41/31.63      inference('demod', [status(thm)], ['44', '47', '50'])).
% 31.41/31.63  thf('74', plain,
% 31.41/31.63      (![X37 : $i]:
% 31.41/31.63         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 31.41/31.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 31.41/31.63      inference('demod', [status(thm)], ['53', '54'])).
% 31.41/31.63  thf('75', plain,
% 31.41/31.63      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 31.41/31.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 31.41/31.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 31.41/31.63          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 31.41/31.63          | ((X17) != (X20)))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 31.41/31.63  thf('76', plain,
% 31.41/31.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 31.41/31.63         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 31.41/31.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 31.41/31.63      inference('simplify', [status(thm)], ['75'])).
% 31.41/31.63  thf('77', plain,
% 31.41/31.63      (![X0 : $i]:
% 31.41/31.63         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 31.41/31.63      inference('sup-', [status(thm)], ['74', '76'])).
% 31.41/31.63  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 31.41/31.63      inference('sup-', [status(thm)], ['45', '46'])).
% 31.41/31.63  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('80', plain, ((v2_funct_1 @ sk_B)),
% 31.41/31.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 31.41/31.63  thf('81', plain,
% 31.41/31.63      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['72', '73', '77', '78', '79', '80'])).
% 31.41/31.63  thf('82', plain,
% 31.41/31.63      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 31.41/31.63         = (k6_relat_1 @ sk_A))),
% 31.41/31.63      inference('demod', [status(thm)], ['34', '35', '81'])).
% 31.41/31.63  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 31.41/31.63  thf('84', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63           (k6_partfun1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('split', [status(esa)], ['1'])).
% 31.41/31.63  thf('85', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 31.41/31.63  thf('86', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63           (k6_relat_1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('demod', [status(thm)], ['84', '85'])).
% 31.41/31.63  thf('87', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 31.41/31.63            sk_B) @ 
% 31.41/31.63           (k6_relat_1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('sup-', [status(thm)], ['83', '86'])).
% 31.41/31.63  thf('88', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 31.41/31.63           (k6_relat_1 @ sk_A)))
% 31.41/31.63         <= (~
% 31.41/31.63             ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63               (k6_partfun1 @ sk_A))))),
% 31.41/31.63      inference('sup-', [status(thm)], ['82', '87'])).
% 31.41/31.63  thf('89', plain,
% 31.41/31.63      (![X0 : $i]:
% 31.41/31.63         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 31.41/31.63      inference('sup-', [status(thm)], ['74', '76'])).
% 31.41/31.63  thf('90', plain,
% 31.41/31.63      (((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63         (k6_partfun1 @ sk_A)))),
% 31.41/31.63      inference('demod', [status(thm)], ['88', '89'])).
% 31.41/31.63  thf('91', plain,
% 31.41/31.63      (~
% 31.41/31.63       ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63         (k6_partfun1 @ sk_A))) | 
% 31.41/31.63       ~
% 31.41/31.63       ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 31.41/31.63          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 31.41/31.63         (k6_partfun1 @ sk_A)))),
% 31.41/31.63      inference('split', [status(esa)], ['1'])).
% 31.41/31.63  thf('92', plain,
% 31.41/31.63      (~
% 31.41/31.63       ((r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 31.41/31.63         (k6_partfun1 @ sk_A)))),
% 31.41/31.63      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 31.41/31.63  thf('93', plain,
% 31.41/31.63      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 31.41/31.63          (k6_relat_1 @ sk_A))),
% 31.41/31.63      inference('simpl_trail', [status(thm)], ['12', '92'])).
% 31.41/31.63  thf('94', plain,
% 31.41/31.63      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 31.41/31.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 31.41/31.63  thf('95', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 31.41/31.63  thf('96', plain,
% 31.41/31.63      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 31.41/31.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('demod', [status(thm)], ['94', '95'])).
% 31.41/31.63  thf('97', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('98', plain,
% 31.41/31.63      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 31.41/31.63         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 31.41/31.63          | ~ (v1_funct_1 @ X38)
% 31.41/31.63          | ~ (v1_funct_1 @ X41)
% 31.41/31.63          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 31.41/31.63          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 31.41/31.63              = (k5_relat_1 @ X38 @ X41)))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 31.41/31.63  thf('99', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.41/31.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 31.41/31.63            = (k5_relat_1 @ sk_B @ X0))
% 31.41/31.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 31.41/31.63          | ~ (v1_funct_1 @ X0)
% 31.41/31.63          | ~ (v1_funct_1 @ sk_B))),
% 31.41/31.63      inference('sup-', [status(thm)], ['97', '98'])).
% 31.41/31.63  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('101', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.41/31.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 31.41/31.63            = (k5_relat_1 @ sk_B @ X0))
% 31.41/31.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 31.41/31.63          | ~ (v1_funct_1 @ X0))),
% 31.41/31.63      inference('demod', [status(thm)], ['99', '100'])).
% 31.41/31.63  thf('102', plain,
% 31.41/31.63      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 31.41/31.63        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 31.41/31.63            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 31.41/31.63      inference('sup-', [status(thm)], ['96', '101'])).
% 31.41/31.63  thf('103', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 31.41/31.63  thf('104', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 31.41/31.63  thf('105', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['103', '104'])).
% 31.41/31.63  thf('106', plain,
% 31.41/31.63      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 31.41/31.63         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 31.41/31.63      inference('demod', [status(thm)], ['102', '105'])).
% 31.41/31.63  thf('107', plain,
% 31.41/31.63      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 31.41/31.63          (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A))),
% 31.41/31.63      inference('demod', [status(thm)], ['93', '106'])).
% 31.41/31.63  thf('108', plain,
% 31.41/31.63      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 31.41/31.63           (k6_relat_1 @ sk_A))
% 31.41/31.63        | ~ (v1_relat_1 @ sk_B)
% 31.41/31.63        | ~ (v1_funct_1 @ sk_B)
% 31.41/31.63        | ~ (v2_funct_1 @ sk_B))),
% 31.41/31.63      inference('sup-', [status(thm)], ['0', '107'])).
% 31.41/31.63  thf('109', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(d1_funct_2, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i]:
% 31.41/31.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.41/31.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 31.41/31.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 31.41/31.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 31.41/31.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 31.41/31.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 31.41/31.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 31.41/31.63  thf(zf_stmt_1, axiom,
% 31.41/31.63    (![C:$i,B:$i,A:$i]:
% 31.41/31.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 31.41/31.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 31.41/31.63  thf('110', plain,
% 31.41/31.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 31.41/31.63         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 31.41/31.63          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 31.41/31.63          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 31.41/31.63  thf('111', plain,
% 31.41/31.63      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 31.41/31.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 31.41/31.63      inference('sup-', [status(thm)], ['109', '110'])).
% 31.41/31.63  thf('112', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 31.41/31.63  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 31.41/31.63  thf(zf_stmt_4, axiom,
% 31.41/31.63    (![B:$i,A:$i]:
% 31.41/31.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 31.41/31.63       ( zip_tseitin_0 @ B @ A ) ))).
% 31.41/31.63  thf(zf_stmt_5, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i]:
% 31.41/31.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.41/31.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 31.41/31.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 31.41/31.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 31.41/31.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 31.41/31.63  thf('113', plain,
% 31.41/31.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 31.41/31.63         (~ (zip_tseitin_0 @ X29 @ X30)
% 31.41/31.63          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 31.41/31.63          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 31.41/31.63  thf('114', plain,
% 31.41/31.63      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 31.41/31.63      inference('sup-', [status(thm)], ['112', '113'])).
% 31.41/31.63  thf('115', plain,
% 31.41/31.63      (![X24 : $i, X25 : $i]:
% 31.41/31.63         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 31.41/31.63  thf('116', plain,
% 31.41/31.63      (![X24 : $i, X25 : $i]:
% 31.41/31.63         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 31.41/31.63  thf('117', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 31.41/31.63      inference('simplify', [status(thm)], ['116'])).
% 31.41/31.63  thf('118', plain,
% 31.41/31.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.41/31.63         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 31.41/31.63      inference('sup+', [status(thm)], ['115', '117'])).
% 31.41/31.63  thf('119', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 31.41/31.63      inference('eq_fact', [status(thm)], ['118'])).
% 31.41/31.63  thf('120', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 31.41/31.63      inference('demod', [status(thm)], ['114', '119'])).
% 31.41/31.63  thf('121', plain,
% 31.41/31.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf(redefinition_k1_relset_1, axiom,
% 31.41/31.63    (![A:$i,B:$i,C:$i]:
% 31.41/31.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.41/31.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 31.41/31.63  thf('122', plain,
% 31.41/31.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 31.41/31.63         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 31.41/31.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 31.41/31.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 31.41/31.63  thf('123', plain,
% 31.41/31.63      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 31.41/31.63      inference('sup-', [status(thm)], ['121', '122'])).
% 31.41/31.63  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 31.41/31.63      inference('demod', [status(thm)], ['111', '120', '123'])).
% 31.41/31.63  thf('125', plain,
% 31.41/31.63      (![X0 : $i]:
% 31.41/31.63         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 31.41/31.63      inference('sup-', [status(thm)], ['74', '76'])).
% 31.41/31.63  thf('126', plain, ((v1_relat_1 @ sk_B)),
% 31.41/31.63      inference('sup-', [status(thm)], ['45', '46'])).
% 31.41/31.63  thf('127', plain, ((v1_funct_1 @ sk_B)),
% 31.41/31.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.41/31.63  thf('128', plain, ((v2_funct_1 @ sk_B)),
% 31.41/31.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 31.41/31.63  thf('129', plain, ($false),
% 31.41/31.63      inference('demod', [status(thm)],
% 31.41/31.63                ['108', '124', '125', '126', '127', '128'])).
% 31.41/31.63  
% 31.41/31.63  % SZS output end Refutation
% 31.41/31.63  
% 31.41/31.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
