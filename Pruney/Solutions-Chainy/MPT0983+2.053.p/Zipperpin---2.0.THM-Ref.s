%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5dNvIg2EXU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:09 EST 2020

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 369 expanded)
%              Number of leaves         :   43 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          : 1278 (7541 expanded)
%              Number of equality atoms :   47 (  99 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('5',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('7',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('15',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_relat_1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['31','34','35','38'])).

thf('40',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['9','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('50',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('58',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47 ) )
      | ( v2_funct_1 @ X51 )
      | ( X49 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X48 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('69',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('70',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['67','70'])).

thf('72',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('73',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','84'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('86',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','87'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('89',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('90',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['47','94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['44','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5dNvIg2EXU
% 0.14/0.37  % Computer   : n011.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:37:27 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 2.71/2.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.71/2.98  % Solved by: fo/fo7.sh
% 2.71/2.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.71/2.98  % done 3329 iterations in 2.504s
% 2.71/2.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.71/2.98  % SZS output start Refutation
% 2.71/2.98  thf(sk_B_type, type, sk_B: $i).
% 2.71/2.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.71/2.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.71/2.98  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.71/2.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.71/2.98  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.71/2.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.71/2.98  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.71/2.98  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.71/2.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.71/2.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.71/2.98  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.71/2.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.71/2.98  thf(sk_A_type, type, sk_A: $i).
% 2.71/2.98  thf(sk_D_type, type, sk_D: $i).
% 2.71/2.98  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.71/2.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.71/2.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.71/2.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.71/2.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.71/2.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.71/2.98  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.71/2.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.71/2.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.71/2.98  thf(sk_C_type, type, sk_C: $i).
% 2.71/2.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.71/2.98  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.71/2.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.71/2.98  thf(t8_boole, axiom,
% 2.71/2.98    (![A:$i,B:$i]:
% 2.71/2.98     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.71/2.98  thf('1', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i]:
% 2.71/2.98         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.71/2.98      inference('cnf', [status(esa)], [t8_boole])).
% 2.71/2.98  thf('2', plain,
% 2.71/2.98      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.71/2.98      inference('sup-', [status(thm)], ['0', '1'])).
% 2.71/2.98  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.71/2.98  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.71/2.98      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.71/2.98  thf(fc4_funct_1, axiom,
% 2.71/2.98    (![A:$i]:
% 2.71/2.98     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.71/2.98       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.71/2.98  thf('4', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 2.71/2.98      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.71/2.98  thf('5', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.71/2.98      inference('sup+', [status(thm)], ['3', '4'])).
% 2.71/2.98  thf('6', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.71/2.98      inference('sup+', [status(thm)], ['2', '5'])).
% 2.71/2.98  thf(t29_funct_2, conjecture,
% 2.71/2.98    (![A:$i,B:$i,C:$i]:
% 2.71/2.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.71/2.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.98       ( ![D:$i]:
% 2.71/2.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.71/2.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.71/2.98           ( ( r2_relset_1 @
% 2.71/2.98               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.71/2.98               ( k6_partfun1 @ A ) ) =>
% 2.71/2.98             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.71/2.98  thf(zf_stmt_0, negated_conjecture,
% 2.71/2.98    (~( ![A:$i,B:$i,C:$i]:
% 2.71/2.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.71/2.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.98          ( ![D:$i]:
% 2.71/2.98            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.71/2.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.71/2.98              ( ( r2_relset_1 @
% 2.71/2.98                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.71/2.98                  ( k6_partfun1 @ A ) ) =>
% 2.71/2.98                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.71/2.98    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.71/2.98  thf('7', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('8', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.98      inference('split', [status(esa)], ['7'])).
% 2.71/2.98  thf('9', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.98      inference('sup-', [status(thm)], ['6', '8'])).
% 2.71/2.98  thf('10', plain,
% 2.71/2.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.98        (k6_partfun1 @ sk_A))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(redefinition_k6_partfun1, axiom,
% 2.71/2.98    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.71/2.98  thf('11', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.71/2.98  thf('12', plain,
% 2.71/2.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.98        (k6_relat_1 @ sk_A))),
% 2.71/2.98      inference('demod', [status(thm)], ['10', '11'])).
% 2.71/2.98  thf('13', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(t24_funct_2, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i]:
% 2.71/2.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.71/2.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.98       ( ![D:$i]:
% 2.71/2.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.71/2.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.71/2.98           ( ( r2_relset_1 @
% 2.71/2.98               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.71/2.98               ( k6_partfun1 @ B ) ) =>
% 2.71/2.98             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.71/2.98  thf('14', plain,
% 2.71/2.98      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X43)
% 2.71/2.98          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.71/2.98          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.71/2.98          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 2.71/2.98               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 2.71/2.98               (k6_partfun1 @ X44))
% 2.71/2.98          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 2.71/2.98          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.71/2.98          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 2.71/2.98          | ~ (v1_funct_1 @ X46))),
% 2.71/2.98      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.71/2.98  thf('15', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.71/2.98  thf('16', plain,
% 2.71/2.98      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X43)
% 2.71/2.98          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.71/2.98          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.71/2.98          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 2.71/2.98               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 2.71/2.98               (k6_relat_1 @ X44))
% 2.71/2.98          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 2.71/2.98          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.71/2.98          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 2.71/2.98          | ~ (v1_funct_1 @ X46))),
% 2.71/2.98      inference('demod', [status(thm)], ['14', '15'])).
% 2.71/2.98  thf('17', plain,
% 2.71/2.98      (![X0 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X0)
% 2.71/2.98          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.71/2.98          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.71/2.98          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.98               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.71/2.98               (k6_relat_1 @ sk_A))
% 2.71/2.98          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.71/2.98          | ~ (v1_funct_1 @ sk_C))),
% 2.71/2.98      inference('sup-', [status(thm)], ['13', '16'])).
% 2.71/2.98  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('20', plain,
% 2.71/2.98      (![X0 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X0)
% 2.71/2.98          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.71/2.98          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.71/2.98          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.98               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.71/2.98               (k6_relat_1 @ sk_A)))),
% 2.71/2.98      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.71/2.98  thf('21', plain,
% 2.71/2.98      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.71/2.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.71/2.98        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.71/2.98        | ~ (v1_funct_1 @ sk_D))),
% 2.71/2.98      inference('sup-', [status(thm)], ['12', '20'])).
% 2.71/2.98  thf('22', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(redefinition_k2_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i]:
% 2.71/2.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.71/2.98  thf('23', plain,
% 2.71/2.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.71/2.98         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.71/2.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.71/2.98  thf('24', plain,
% 2.71/2.98      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.71/2.98      inference('sup-', [status(thm)], ['22', '23'])).
% 2.71/2.98  thf('25', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.71/2.98      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 2.71/2.98  thf(d3_funct_2, axiom,
% 2.71/2.98    (![A:$i,B:$i]:
% 2.71/2.98     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.71/2.98       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.71/2.98  thf('29', plain,
% 2.71/2.98      (![X32 : $i, X33 : $i]:
% 2.71/2.98         (((k2_relat_1 @ X33) != (X32))
% 2.71/2.98          | (v2_funct_2 @ X33 @ X32)
% 2.71/2.98          | ~ (v5_relat_1 @ X33 @ X32)
% 2.71/2.98          | ~ (v1_relat_1 @ X33))),
% 2.71/2.98      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.71/2.98  thf('30', plain,
% 2.71/2.98      (![X33 : $i]:
% 2.71/2.98         (~ (v1_relat_1 @ X33)
% 2.71/2.98          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 2.71/2.98          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 2.71/2.98      inference('simplify', [status(thm)], ['29'])).
% 2.71/2.98  thf('31', plain,
% 2.71/2.98      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.71/2.98        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.71/2.98        | ~ (v1_relat_1 @ sk_D))),
% 2.71/2.98      inference('sup-', [status(thm)], ['28', '30'])).
% 2.71/2.98  thf('32', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(cc2_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i]:
% 2.71/2.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.71/2.98  thf('33', plain,
% 2.71/2.98      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.71/2.98         ((v5_relat_1 @ X7 @ X9)
% 2.71/2.98          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.71/2.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.71/2.98  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.71/2.98      inference('sup-', [status(thm)], ['32', '33'])).
% 2.71/2.98  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.71/2.98      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 2.71/2.98  thf('36', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(cc1_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i]:
% 2.71/2.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.98       ( v1_relat_1 @ C ) ))).
% 2.71/2.98  thf('37', plain,
% 2.71/2.98      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.71/2.98         ((v1_relat_1 @ X4)
% 2.71/2.98          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 2.71/2.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.71/2.98  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 2.71/2.98      inference('sup-', [status(thm)], ['36', '37'])).
% 2.71/2.98  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.71/2.98      inference('demod', [status(thm)], ['31', '34', '35', '38'])).
% 2.71/2.98  thf('40', plain,
% 2.71/2.98      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.71/2.98      inference('split', [status(esa)], ['7'])).
% 2.71/2.98  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.71/2.98      inference('sup-', [status(thm)], ['39', '40'])).
% 2.71/2.98  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.71/2.98      inference('split', [status(esa)], ['7'])).
% 2.71/2.98  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.71/2.98      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 2.71/2.98  thf('44', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.71/2.98      inference('simpl_trail', [status(thm)], ['9', '43'])).
% 2.71/2.98  thf('45', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(cc3_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i]:
% 2.71/2.98     ( ( v1_xboole_0 @ A ) =>
% 2.71/2.98       ( ![C:$i]:
% 2.71/2.98         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.71/2.98           ( v1_xboole_0 @ C ) ) ) ))).
% 2.71/2.98  thf('46', plain,
% 2.71/2.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.71/2.98         (~ (v1_xboole_0 @ X10)
% 2.71/2.98          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 2.71/2.98          | (v1_xboole_0 @ X11))),
% 2.71/2.98      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.71/2.98  thf('47', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.71/2.98      inference('sup-', [status(thm)], ['45', '46'])).
% 2.71/2.98  thf('48', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('49', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(redefinition_k1_partfun1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.71/2.98     ( ( ( v1_funct_1 @ E ) & 
% 2.71/2.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.71/2.98         ( v1_funct_1 @ F ) & 
% 2.71/2.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.71/2.98       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.71/2.98  thf('50', plain,
% 2.71/2.98      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.71/2.98         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.71/2.98          | ~ (v1_funct_1 @ X36)
% 2.71/2.98          | ~ (v1_funct_1 @ X39)
% 2.71/2.98          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.71/2.98          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 2.71/2.98              = (k5_relat_1 @ X36 @ X39)))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.71/2.98  thf('51', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.71/2.98            = (k5_relat_1 @ sk_C @ X0))
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.71/2.98          | ~ (v1_funct_1 @ X0)
% 2.71/2.98          | ~ (v1_funct_1 @ sk_C))),
% 2.71/2.98      inference('sup-', [status(thm)], ['49', '50'])).
% 2.71/2.98  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('53', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.71/2.98            = (k5_relat_1 @ sk_C @ X0))
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.71/2.98          | ~ (v1_funct_1 @ X0))),
% 2.71/2.98      inference('demod', [status(thm)], ['51', '52'])).
% 2.71/2.98  thf('54', plain,
% 2.71/2.98      ((~ (v1_funct_1 @ sk_D)
% 2.71/2.98        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.98            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.71/2.98      inference('sup-', [status(thm)], ['48', '53'])).
% 2.71/2.98  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('56', plain,
% 2.71/2.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.98         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.71/2.98      inference('demod', [status(thm)], ['54', '55'])).
% 2.71/2.98  thf('57', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(t26_funct_2, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i,D:$i]:
% 2.71/2.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.71/2.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.98       ( ![E:$i]:
% 2.71/2.98         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.71/2.98             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.71/2.98           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.71/2.98             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.71/2.98               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.71/2.98  thf('58', plain,
% 2.71/2.98      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X47)
% 2.71/2.98          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 2.71/2.98          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 2.71/2.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 2.71/2.98          | (v2_funct_1 @ X51)
% 2.71/2.98          | ((X49) = (k1_xboole_0))
% 2.71/2.98          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.71/2.98          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 2.71/2.98          | ~ (v1_funct_1 @ X51))),
% 2.71/2.98      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.71/2.98  thf('59', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X0)
% 2.71/2.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.71/2.98          | ((sk_A) = (k1_xboole_0))
% 2.71/2.98          | (v2_funct_1 @ X0)
% 2.71/2.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.71/2.98          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.71/2.98          | ~ (v1_funct_1 @ sk_D))),
% 2.71/2.98      inference('sup-', [status(thm)], ['57', '58'])).
% 2.71/2.98  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('62', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i]:
% 2.71/2.98         (~ (v1_funct_1 @ X0)
% 2.71/2.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.71/2.98          | ((sk_A) = (k1_xboole_0))
% 2.71/2.98          | (v2_funct_1 @ X0)
% 2.71/2.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.71/2.98      inference('demod', [status(thm)], ['59', '60', '61'])).
% 2.71/2.98  thf('63', plain,
% 2.71/2.98      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.71/2.98        | (v2_funct_1 @ sk_C)
% 2.71/2.98        | ((sk_A) = (k1_xboole_0))
% 2.71/2.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.71/2.98        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.71/2.98        | ~ (v1_funct_1 @ sk_C))),
% 2.71/2.98      inference('sup-', [status(thm)], ['56', '62'])).
% 2.71/2.98  thf('64', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('67', plain,
% 2.71/2.98      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.71/2.98        | (v2_funct_1 @ sk_C)
% 2.71/2.98        | ((sk_A) = (k1_xboole_0)))),
% 2.71/2.98      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 2.71/2.98  thf('68', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.71/2.98      inference('split', [status(esa)], ['7'])).
% 2.71/2.98  thf('69', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.71/2.98      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 2.71/2.98  thf('70', plain, (~ (v2_funct_1 @ sk_C)),
% 2.71/2.98      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 2.71/2.98  thf('71', plain,
% 2.71/2.98      ((((sk_A) = (k1_xboole_0)) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 2.71/2.98      inference('clc', [status(thm)], ['67', '70'])).
% 2.71/2.98  thf('72', plain,
% 2.71/2.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.71/2.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.98        (k6_relat_1 @ sk_A))),
% 2.71/2.98      inference('demod', [status(thm)], ['10', '11'])).
% 2.71/2.98  thf('73', plain,
% 2.71/2.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.98         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.71/2.98      inference('demod', [status(thm)], ['54', '55'])).
% 2.71/2.98  thf('74', plain,
% 2.71/2.98      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.71/2.98        (k6_relat_1 @ sk_A))),
% 2.71/2.98      inference('demod', [status(thm)], ['72', '73'])).
% 2.71/2.98  thf('75', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('76', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(dt_k4_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.71/2.98     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.71/2.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.71/2.98       ( m1_subset_1 @
% 2.71/2.98         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.71/2.98         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.71/2.98  thf('77', plain,
% 2.71/2.98      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.71/2.98         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 2.71/2.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.71/2.98          | (m1_subset_1 @ (k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16) @ 
% 2.71/2.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X18))))),
% 2.71/2.98      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.71/2.98  thf('78', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.98         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.71/2.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.71/2.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.71/2.98      inference('sup-', [status(thm)], ['76', '77'])).
% 2.71/2.98  thf('79', plain,
% 2.71/2.98      ((m1_subset_1 @ 
% 2.71/2.98        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.71/2.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.71/2.98      inference('sup-', [status(thm)], ['75', '78'])).
% 2.71/2.98  thf('80', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf('81', plain,
% 2.71/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.71/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.98  thf(redefinition_k4_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.71/2.98     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.71/2.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.71/2.98       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.71/2.98  thf('82', plain,
% 2.71/2.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.71/2.98         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.71/2.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.71/2.98          | ((k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 2.71/2.98              = (k5_relat_1 @ X22 @ X25)))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.71/2.98  thf('83', plain,
% 2.71/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.98         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.71/2.98            = (k5_relat_1 @ sk_C @ X0))
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.71/2.98      inference('sup-', [status(thm)], ['81', '82'])).
% 2.71/2.98  thf('84', plain,
% 2.71/2.98      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.71/2.98         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.71/2.98      inference('sup-', [status(thm)], ['80', '83'])).
% 2.71/2.98  thf('85', plain,
% 2.71/2.98      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.71/2.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.71/2.98      inference('demod', [status(thm)], ['79', '84'])).
% 2.71/2.98  thf(redefinition_r2_relset_1, axiom,
% 2.71/2.98    (![A:$i,B:$i,C:$i,D:$i]:
% 2.71/2.98     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.71/2.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.71/2.98       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.71/2.98  thf('86', plain,
% 2.71/2.98      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.71/2.98         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.71/2.98          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.71/2.98          | ((X28) = (X31))
% 2.71/2.98          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.71/2.98  thf('87', plain,
% 2.71/2.98      (![X0 : $i]:
% 2.71/2.98         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.71/2.98          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.71/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.71/2.98      inference('sup-', [status(thm)], ['85', '86'])).
% 2.71/2.98  thf('88', plain,
% 2.71/2.98      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.71/2.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.71/2.98        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.71/2.98      inference('sup-', [status(thm)], ['74', '87'])).
% 2.71/2.98  thf(dt_k6_partfun1, axiom,
% 2.71/2.98    (![A:$i]:
% 2.71/2.98     ( ( m1_subset_1 @
% 2.71/2.98         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.71/2.98       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.71/2.98  thf('89', plain,
% 2.71/2.98      (![X35 : $i]:
% 2.71/2.98         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 2.71/2.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 2.71/2.98      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.71/2.98  thf('90', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.71/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.71/2.98  thf('91', plain,
% 2.71/2.98      (![X35 : $i]:
% 2.71/2.98         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 2.71/2.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 2.71/2.98      inference('demod', [status(thm)], ['89', '90'])).
% 2.71/2.98  thf('92', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.71/2.98      inference('demod', [status(thm)], ['88', '91'])).
% 2.71/2.98  thf('93', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 2.71/2.98      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.71/2.98  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 2.71/2.98      inference('demod', [status(thm)], ['71', '92', '93'])).
% 2.71/2.98  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.71/2.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.71/2.98  thf('96', plain, ((v1_xboole_0 @ sk_C)),
% 2.71/2.98      inference('demod', [status(thm)], ['47', '94', '95'])).
% 2.71/2.98  thf('97', plain, ($false), inference('demod', [status(thm)], ['44', '96'])).
% 2.71/2.98  
% 2.71/2.98  % SZS output end Refutation
% 2.71/2.98  
% 2.71/2.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
