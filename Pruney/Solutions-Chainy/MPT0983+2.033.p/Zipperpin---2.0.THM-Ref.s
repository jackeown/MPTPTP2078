%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tp4AnHesIk

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:06 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 353 expanded)
%              Number of leaves         :   43 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          : 1244 (7273 expanded)
%              Number of equality atoms :   53 (  90 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('7',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

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

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
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

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( ( k2_relat_1 @ X35 )
       != X34 )
      | ( v2_funct_2 @ X35 @ X34 )
      | ~ ( v5_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X35: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v5_relat_1 @ X35 @ ( k2_relat_1 @ X35 ) )
      | ( v2_funct_2 @ X35 @ ( k2_relat_1 @ X35 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    inference(split,[status(esa)],['11'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
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

thf('68',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('70',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('78',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('82',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('85',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('86',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('90',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','88','89'])).

thf('91',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('92',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('93',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['90','93'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('95',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['47','94','96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['44','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tp4AnHesIk
% 0.13/0.36  % Computer   : n004.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:22:54 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 3.34/3.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.34/3.57  % Solved by: fo/fo7.sh
% 3.34/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.34/3.57  % done 3713 iterations in 3.092s
% 3.34/3.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.34/3.57  % SZS output start Refutation
% 3.34/3.57  thf(sk_D_type, type, sk_D: $i).
% 3.34/3.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.34/3.57  thf(sk_B_type, type, sk_B: $i).
% 3.34/3.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.34/3.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.34/3.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.34/3.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.34/3.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.34/3.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.34/3.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.34/3.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.34/3.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.34/3.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.34/3.57  thf(sk_C_type, type, sk_C: $i).
% 3.34/3.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.34/3.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.34/3.57  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 3.34/3.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.34/3.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.34/3.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.34/3.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.34/3.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.34/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.34/3.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.34/3.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.34/3.57  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.57  thf(t8_boole, axiom,
% 3.34/3.57    (![A:$i,B:$i]:
% 3.34/3.57     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.34/3.57  thf('1', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i]:
% 3.34/3.57         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.34/3.57      inference('cnf', [status(esa)], [t8_boole])).
% 3.34/3.57  thf('2', plain,
% 3.34/3.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.57      inference('sup-', [status(thm)], ['0', '1'])).
% 3.34/3.57  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.34/3.57  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.57      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.34/3.57  thf(redefinition_k6_partfun1, axiom,
% 3.34/3.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.34/3.57  thf('4', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.57  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.57      inference('demod', [status(thm)], ['3', '4'])).
% 3.34/3.57  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.34/3.57  thf('6', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 3.34/3.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.34/3.57  thf('7', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.57  thf('8', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 3.34/3.57      inference('demod', [status(thm)], ['6', '7'])).
% 3.34/3.57  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.34/3.57      inference('sup+', [status(thm)], ['5', '8'])).
% 3.34/3.57  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.57      inference('sup+', [status(thm)], ['2', '9'])).
% 3.34/3.57  thf(t29_funct_2, conjecture,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57       ( ![D:$i]:
% 3.34/3.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.57           ( ( r2_relset_1 @
% 3.34/3.57               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.34/3.57               ( k6_partfun1 @ A ) ) =>
% 3.34/3.57             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.34/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.34/3.57    (~( ![A:$i,B:$i,C:$i]:
% 3.34/3.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57          ( ![D:$i]:
% 3.34/3.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.57              ( ( r2_relset_1 @
% 3.34/3.57                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.34/3.57                  ( k6_partfun1 @ A ) ) =>
% 3.34/3.57                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.34/3.57    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.34/3.57  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.34/3.57      inference('split', [status(esa)], ['11'])).
% 3.34/3.57  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.34/3.57      inference('sup-', [status(thm)], ['10', '12'])).
% 3.34/3.57  thf('14', plain,
% 3.34/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.57        (k6_partfun1 @ sk_A))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('15', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(t24_funct_2, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57       ( ![D:$i]:
% 3.34/3.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.57           ( ( r2_relset_1 @
% 3.34/3.57               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.34/3.57               ( k6_partfun1 @ B ) ) =>
% 3.34/3.57             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.34/3.57  thf('16', plain,
% 3.34/3.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X43)
% 3.34/3.57          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 3.34/3.57          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 3.34/3.57          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 3.34/3.57               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 3.34/3.57               (k6_partfun1 @ X44))
% 3.34/3.57          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 3.34/3.57          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 3.34/3.57          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 3.34/3.57          | ~ (v1_funct_1 @ X46))),
% 3.34/3.57      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.34/3.57  thf('17', plain,
% 3.34/3.57      (![X0 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.34/3.57          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.34/3.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.34/3.57               (k6_partfun1 @ sk_A))
% 3.34/3.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.34/3.57          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.57      inference('sup-', [status(thm)], ['15', '16'])).
% 3.34/3.57  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('20', plain,
% 3.34/3.57      (![X0 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.34/3.57          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.34/3.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.34/3.57               (k6_partfun1 @ sk_A)))),
% 3.34/3.57      inference('demod', [status(thm)], ['17', '18', '19'])).
% 3.34/3.57  thf('21', plain,
% 3.34/3.57      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.34/3.57        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.34/3.57        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.34/3.57        | ~ (v1_funct_1 @ sk_D))),
% 3.34/3.57      inference('sup-', [status(thm)], ['14', '20'])).
% 3.34/3.57  thf('22', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(redefinition_k2_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.34/3.57  thf('23', plain,
% 3.34/3.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.34/3.57         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 3.34/3.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.34/3.57  thf('24', plain,
% 3.34/3.57      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.34/3.57      inference('sup-', [status(thm)], ['22', '23'])).
% 3.34/3.57  thf('25', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.57      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.34/3.57  thf(d3_funct_2, axiom,
% 3.34/3.57    (![A:$i,B:$i]:
% 3.34/3.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.34/3.57       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.34/3.57  thf('29', plain,
% 3.34/3.57      (![X34 : $i, X35 : $i]:
% 3.34/3.57         (((k2_relat_1 @ X35) != (X34))
% 3.34/3.57          | (v2_funct_2 @ X35 @ X34)
% 3.34/3.57          | ~ (v5_relat_1 @ X35 @ X34)
% 3.34/3.57          | ~ (v1_relat_1 @ X35))),
% 3.34/3.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.34/3.57  thf('30', plain,
% 3.34/3.57      (![X35 : $i]:
% 3.34/3.57         (~ (v1_relat_1 @ X35)
% 3.34/3.57          | ~ (v5_relat_1 @ X35 @ (k2_relat_1 @ X35))
% 3.34/3.57          | (v2_funct_2 @ X35 @ (k2_relat_1 @ X35)))),
% 3.34/3.57      inference('simplify', [status(thm)], ['29'])).
% 3.34/3.57  thf('31', plain,
% 3.34/3.57      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.34/3.57        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.34/3.57        | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.57      inference('sup-', [status(thm)], ['28', '30'])).
% 3.34/3.57  thf('32', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(cc2_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.34/3.57  thf('33', plain,
% 3.34/3.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.34/3.57         ((v5_relat_1 @ X11 @ X13)
% 3.34/3.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.34/3.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.34/3.57  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.34/3.57      inference('sup-', [status(thm)], ['32', '33'])).
% 3.34/3.57  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.57      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.34/3.57  thf('36', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(cc1_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.57       ( v1_relat_1 @ C ) ))).
% 3.34/3.57  thf('37', plain,
% 3.34/3.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.34/3.57         ((v1_relat_1 @ X8)
% 3.34/3.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.34/3.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.34/3.57  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.57      inference('sup-', [status(thm)], ['36', '37'])).
% 3.34/3.57  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.34/3.57      inference('demod', [status(thm)], ['31', '34', '35', '38'])).
% 3.34/3.57  thf('40', plain,
% 3.34/3.57      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.34/3.57      inference('split', [status(esa)], ['11'])).
% 3.34/3.57  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.34/3.57      inference('sup-', [status(thm)], ['39', '40'])).
% 3.34/3.57  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.34/3.57      inference('split', [status(esa)], ['11'])).
% 3.34/3.57  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.34/3.57      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 3.34/3.57  thf('44', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.34/3.57      inference('simpl_trail', [status(thm)], ['13', '43'])).
% 3.34/3.57  thf('45', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(cc1_subset_1, axiom,
% 3.34/3.57    (![A:$i]:
% 3.34/3.57     ( ( v1_xboole_0 @ A ) =>
% 3.34/3.57       ( ![B:$i]:
% 3.34/3.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.34/3.57  thf('46', plain,
% 3.34/3.57      (![X5 : $i, X6 : $i]:
% 3.34/3.57         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.34/3.57          | (v1_xboole_0 @ X5)
% 3.34/3.57          | ~ (v1_xboole_0 @ X6))),
% 3.34/3.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.34/3.57  thf('47', plain,
% 3.34/3.57      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.34/3.57      inference('sup-', [status(thm)], ['45', '46'])).
% 3.34/3.57  thf('48', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('49', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(redefinition_k1_partfun1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.34/3.57     ( ( ( v1_funct_1 @ E ) & 
% 3.34/3.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.57         ( v1_funct_1 @ F ) & 
% 3.34/3.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.34/3.57       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.34/3.57  thf('50', plain,
% 3.34/3.57      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.34/3.57         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.34/3.57          | ~ (v1_funct_1 @ X36)
% 3.34/3.57          | ~ (v1_funct_1 @ X39)
% 3.34/3.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.34/3.57          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 3.34/3.57              = (k5_relat_1 @ X36 @ X39)))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.34/3.57  thf('51', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.34/3.57            = (k5_relat_1 @ sk_C @ X0))
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.34/3.57          | ~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.57      inference('sup-', [status(thm)], ['49', '50'])).
% 3.34/3.57  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('53', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.34/3.57            = (k5_relat_1 @ sk_C @ X0))
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.34/3.57          | ~ (v1_funct_1 @ X0))),
% 3.34/3.57      inference('demod', [status(thm)], ['51', '52'])).
% 3.34/3.57  thf('54', plain,
% 3.34/3.57      ((~ (v1_funct_1 @ sk_D)
% 3.34/3.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.57            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.34/3.57      inference('sup-', [status(thm)], ['48', '53'])).
% 3.34/3.57  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('56', plain,
% 3.34/3.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.57         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.34/3.57      inference('demod', [status(thm)], ['54', '55'])).
% 3.34/3.57  thf('57', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(t26_funct_2, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.34/3.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57       ( ![E:$i]:
% 3.34/3.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.34/3.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.34/3.57           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.34/3.57             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.34/3.57               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.34/3.57  thf('58', plain,
% 3.34/3.57      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X47)
% 3.34/3.57          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 3.34/3.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.34/3.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 3.34/3.57          | (v2_funct_1 @ X51)
% 3.34/3.57          | ((X49) = (k1_xboole_0))
% 3.34/3.57          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.34/3.57          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 3.34/3.57          | ~ (v1_funct_1 @ X51))),
% 3.34/3.57      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.34/3.57  thf('59', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.34/3.57          | ((sk_A) = (k1_xboole_0))
% 3.34/3.57          | (v2_funct_1 @ X0)
% 3.34/3.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.34/3.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.34/3.57          | ~ (v1_funct_1 @ sk_D))),
% 3.34/3.57      inference('sup-', [status(thm)], ['57', '58'])).
% 3.34/3.57  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('62', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.34/3.57          | ((sk_A) = (k1_xboole_0))
% 3.34/3.57          | (v2_funct_1 @ X0)
% 3.34/3.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.34/3.57      inference('demod', [status(thm)], ['59', '60', '61'])).
% 3.34/3.57  thf('63', plain,
% 3.34/3.57      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.34/3.57        | (v2_funct_1 @ sk_C)
% 3.34/3.57        | ((sk_A) = (k1_xboole_0))
% 3.34/3.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.34/3.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.34/3.57        | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.57      inference('sup-', [status(thm)], ['56', '62'])).
% 3.34/3.57  thf('64', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('67', plain,
% 3.34/3.57      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.34/3.57        | (v2_funct_1 @ sk_C)
% 3.34/3.57        | ((sk_A) = (k1_xboole_0)))),
% 3.34/3.57      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 3.34/3.57  thf('68', plain,
% 3.34/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.57        (k6_partfun1 @ sk_A))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('69', plain,
% 3.34/3.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.57         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.34/3.57      inference('demod', [status(thm)], ['54', '55'])).
% 3.34/3.57  thf('70', plain,
% 3.34/3.57      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.34/3.57        (k6_partfun1 @ sk_A))),
% 3.34/3.57      inference('demod', [status(thm)], ['68', '69'])).
% 3.34/3.57  thf('71', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('72', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(dt_k4_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.34/3.57     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.34/3.57       ( m1_subset_1 @
% 3.34/3.57         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.34/3.57         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 3.34/3.57  thf('73', plain,
% 3.34/3.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.34/3.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 3.34/3.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.34/3.57          | (m1_subset_1 @ (k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17) @ 
% 3.34/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X19))))),
% 3.34/3.57      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 3.34/3.57  thf('74', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.57         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.34/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.34/3.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 3.34/3.57      inference('sup-', [status(thm)], ['72', '73'])).
% 3.34/3.57  thf('75', plain,
% 3.34/3.57      ((m1_subset_1 @ 
% 3.34/3.57        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.34/3.57      inference('sup-', [status(thm)], ['71', '74'])).
% 3.34/3.57  thf('76', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('77', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(redefinition_k4_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.34/3.57     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.34/3.57       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.34/3.57  thf('78', plain,
% 3.34/3.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.34/3.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 3.34/3.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.34/3.57          | ((k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 3.34/3.57              = (k5_relat_1 @ X23 @ X26)))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 3.34/3.57  thf('79', plain,
% 3.34/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.57         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.34/3.57            = (k5_relat_1 @ sk_C @ X0))
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.34/3.57      inference('sup-', [status(thm)], ['77', '78'])).
% 3.34/3.57  thf('80', plain,
% 3.34/3.57      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.57         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.34/3.57      inference('sup-', [status(thm)], ['76', '79'])).
% 3.34/3.57  thf('81', plain,
% 3.34/3.57      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.34/3.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.34/3.57      inference('demod', [status(thm)], ['75', '80'])).
% 3.34/3.57  thf(redefinition_r2_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.34/3.57  thf('82', plain,
% 3.34/3.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.34/3.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.34/3.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.34/3.57          | ((X29) = (X32))
% 3.34/3.57          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.34/3.57  thf('83', plain,
% 3.34/3.57      (![X0 : $i]:
% 3.34/3.57         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.34/3.57          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.34/3.57      inference('sup-', [status(thm)], ['81', '82'])).
% 3.34/3.57  thf('84', plain,
% 3.34/3.57      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.34/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.34/3.57        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.34/3.57      inference('sup-', [status(thm)], ['70', '83'])).
% 3.34/3.57  thf(t29_relset_1, axiom,
% 3.34/3.57    (![A:$i]:
% 3.34/3.57     ( m1_subset_1 @
% 3.34/3.57       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.34/3.57  thf('85', plain,
% 3.34/3.57      (![X33 : $i]:
% 3.34/3.57         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 3.34/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 3.34/3.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.34/3.57  thf('86', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.57  thf('87', plain,
% 3.34/3.57      (![X33 : $i]:
% 3.34/3.57         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 3.34/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 3.34/3.57      inference('demod', [status(thm)], ['85', '86'])).
% 3.34/3.57  thf('88', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.34/3.57      inference('demod', [status(thm)], ['84', '87'])).
% 3.34/3.57  thf('89', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 3.34/3.57      inference('demod', [status(thm)], ['6', '7'])).
% 3.34/3.57  thf('90', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.34/3.57      inference('demod', [status(thm)], ['67', '88', '89'])).
% 3.34/3.57  thf('91', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.34/3.57      inference('split', [status(esa)], ['11'])).
% 3.34/3.57  thf('92', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.34/3.57      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 3.34/3.57  thf('93', plain, (~ (v2_funct_1 @ sk_C)),
% 3.34/3.57      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 3.34/3.57  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 3.34/3.57      inference('clc', [status(thm)], ['90', '93'])).
% 3.34/3.57  thf(t113_zfmisc_1, axiom,
% 3.34/3.57    (![A:$i,B:$i]:
% 3.34/3.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.34/3.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.34/3.57  thf('95', plain,
% 3.34/3.57      (![X3 : $i, X4 : $i]:
% 3.34/3.57         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.34/3.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.34/3.57  thf('96', plain,
% 3.34/3.57      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.34/3.57      inference('simplify', [status(thm)], ['95'])).
% 3.34/3.57  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.57  thf('98', plain, ((v1_xboole_0 @ sk_C)),
% 3.34/3.57      inference('demod', [status(thm)], ['47', '94', '96', '97'])).
% 3.34/3.57  thf('99', plain, ($false), inference('demod', [status(thm)], ['44', '98'])).
% 3.34/3.57  
% 3.34/3.57  % SZS output end Refutation
% 3.34/3.57  
% 3.34/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
