%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rf3y1sEABV

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:24 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 372 expanded)
%              Number of leaves         :   42 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          : 1284 (7574 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['6'])).

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

thf('8',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('15',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_relat_1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
       != X33 )
      | ( v2_funct_2 @ X34 @ X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X34: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ~ ( v5_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
      | ( v2_funct_2 @ X34 @ ( k2_relat_1 @ X34 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['31','34','35','40'])).

thf('42',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('43',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('45',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['9','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46 ) )
      | ( v2_funct_1 @ X50 )
      | ( X48 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X47 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['9','45'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('78',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('83',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','85'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('87',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('91',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','91','92'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['50','93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['47','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rf3y1sEABV
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.73/2.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.73/2.94  % Solved by: fo/fo7.sh
% 2.73/2.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.94  % done 2835 iterations in 2.490s
% 2.73/2.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.73/2.94  % SZS output start Refutation
% 2.73/2.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.73/2.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.73/2.94  thf(sk_C_type, type, sk_C: $i).
% 2.73/2.94  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.73/2.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.73/2.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.73/2.94  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.73/2.94  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.73/2.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.73/2.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.73/2.94  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.73/2.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.73/2.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.73/2.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.73/2.94  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.73/2.94  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.73/2.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.73/2.94  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.73/2.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.73/2.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.73/2.94  thf(sk_B_type, type, sk_B: $i).
% 2.73/2.94  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.94  thf(t29_relset_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( m1_subset_1 @
% 2.73/2.94       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.73/2.94  thf('0', plain,
% 2.73/2.94      (![X32 : $i]:
% 2.73/2.94         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 2.73/2.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 2.73/2.94      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.73/2.94  thf(cc3_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i]:
% 2.73/2.94     ( ( v1_xboole_0 @ A ) =>
% 2.73/2.94       ( ![C:$i]:
% 2.73/2.94         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.94           ( v1_xboole_0 @ C ) ) ) ))).
% 2.73/2.94  thf('1', plain,
% 2.73/2.94      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.73/2.94         (~ (v1_xboole_0 @ X10)
% 2.73/2.94          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 2.73/2.94          | (v1_xboole_0 @ X11))),
% 2.73/2.94      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.73/2.94  thf('2', plain,
% 2.73/2.94      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.73/2.94      inference('sup-', [status(thm)], ['0', '1'])).
% 2.73/2.94  thf(t8_boole, axiom,
% 2.73/2.94    (![A:$i,B:$i]:
% 2.73/2.94     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.73/2.94  thf('3', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.73/2.94      inference('cnf', [status(esa)], [t8_boole])).
% 2.73/2.94  thf('4', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (v1_xboole_0 @ X0)
% 2.73/2.94          | ((k6_relat_1 @ X0) = (X1))
% 2.73/2.94          | ~ (v1_xboole_0 @ X1))),
% 2.73/2.94      inference('sup-', [status(thm)], ['2', '3'])).
% 2.73/2.94  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.73/2.94  thf('5', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.73/2.94      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.73/2.94  thf('6', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 2.73/2.94      inference('sup+', [status(thm)], ['4', '5'])).
% 2.73/2.94  thf('7', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.73/2.94      inference('condensation', [status(thm)], ['6'])).
% 2.73/2.94  thf(t29_funct_2, conjecture,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ![D:$i]:
% 2.73/2.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.94           ( ( r2_relset_1 @
% 2.73/2.94               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.94               ( k6_partfun1 @ A ) ) =>
% 2.73/2.94             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.73/2.94  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.94    (~( ![A:$i,B:$i,C:$i]:
% 2.73/2.94        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94          ( ![D:$i]:
% 2.73/2.94            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.94                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.94              ( ( r2_relset_1 @
% 2.73/2.94                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.94                  ( k6_partfun1 @ A ) ) =>
% 2.73/2.94                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.73/2.94    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.73/2.94  thf('8', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('9', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.73/2.94      inference('split', [status(esa)], ['8'])).
% 2.73/2.94  thf('10', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_partfun1 @ sk_A))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k6_partfun1, axiom,
% 2.73/2.94    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.73/2.94  thf('11', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.94  thf('12', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['10', '11'])).
% 2.73/2.94  thf('13', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(t24_funct_2, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ![D:$i]:
% 2.73/2.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.94           ( ( r2_relset_1 @
% 2.73/2.94               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.73/2.94               ( k6_partfun1 @ B ) ) =>
% 2.73/2.94             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.73/2.94  thf('14', plain,
% 2.73/2.94      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X42)
% 2.73/2.94          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 2.73/2.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.73/2.94          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 2.73/2.94               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 2.73/2.94               (k6_partfun1 @ X43))
% 2.73/2.94          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 2.73/2.94          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 2.73/2.94          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 2.73/2.94          | ~ (v1_funct_1 @ X45))),
% 2.73/2.94      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.73/2.94  thf('15', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.94  thf('16', plain,
% 2.73/2.94      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X42)
% 2.73/2.94          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 2.73/2.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.73/2.94          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 2.73/2.94               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 2.73/2.94               (k6_relat_1 @ X43))
% 2.73/2.94          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 2.73/2.94          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 2.73/2.94          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 2.73/2.94          | ~ (v1_funct_1 @ X45))),
% 2.73/2.94      inference('demod', [status(thm)], ['14', '15'])).
% 2.73/2.94  thf('17', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.94          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.73/2.94          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.73/2.94               (k6_relat_1 @ sk_A))
% 2.73/2.94          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['13', '16'])).
% 2.73/2.94  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('20', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.94          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.73/2.94          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.73/2.94               (k6_relat_1 @ sk_A)))),
% 2.73/2.94      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.73/2.94  thf('21', plain,
% 2.73/2.94      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.73/2.94        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.94        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['12', '20'])).
% 2.73/2.94  thf('22', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k2_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.73/2.94  thf('23', plain,
% 2.73/2.94      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.94         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.73/2.94          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.73/2.94  thf('24', plain,
% 2.73/2.94      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['22', '23'])).
% 2.73/2.94  thf('25', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 2.73/2.94  thf(d3_funct_2, axiom,
% 2.73/2.94    (![A:$i,B:$i]:
% 2.73/2.94     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.73/2.94       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.73/2.94  thf('29', plain,
% 2.73/2.94      (![X33 : $i, X34 : $i]:
% 2.73/2.94         (((k2_relat_1 @ X34) != (X33))
% 2.73/2.94          | (v2_funct_2 @ X34 @ X33)
% 2.73/2.94          | ~ (v5_relat_1 @ X34 @ X33)
% 2.73/2.94          | ~ (v1_relat_1 @ X34))),
% 2.73/2.94      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.73/2.94  thf('30', plain,
% 2.73/2.94      (![X34 : $i]:
% 2.73/2.94         (~ (v1_relat_1 @ X34)
% 2.73/2.94          | ~ (v5_relat_1 @ X34 @ (k2_relat_1 @ X34))
% 2.73/2.94          | (v2_funct_2 @ X34 @ (k2_relat_1 @ X34)))),
% 2.73/2.94      inference('simplify', [status(thm)], ['29'])).
% 2.73/2.94  thf('31', plain,
% 2.73/2.94      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.73/2.94        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.73/2.94        | ~ (v1_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['28', '30'])).
% 2.73/2.94  thf('32', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(cc2_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.73/2.94  thf('33', plain,
% 2.73/2.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.73/2.94         ((v5_relat_1 @ X7 @ X9)
% 2.73/2.94          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.73/2.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.73/2.94  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.73/2.94      inference('sup-', [status(thm)], ['32', '33'])).
% 2.73/2.94  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 2.73/2.94  thf('36', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(cc2_relat_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( v1_relat_1 @ A ) =>
% 2.73/2.94       ( ![B:$i]:
% 2.73/2.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.73/2.94  thf('37', plain,
% 2.73/2.94      (![X2 : $i, X3 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 2.73/2.94          | (v1_relat_1 @ X2)
% 2.73/2.94          | ~ (v1_relat_1 @ X3))),
% 2.73/2.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.73/2.94  thf('38', plain,
% 2.73/2.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['36', '37'])).
% 2.73/2.94  thf(fc6_relat_1, axiom,
% 2.73/2.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.73/2.94  thf('39', plain,
% 2.73/2.94      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.73/2.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.73/2.94  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['38', '39'])).
% 2.73/2.94  thf('41', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.73/2.94      inference('demod', [status(thm)], ['31', '34', '35', '40'])).
% 2.73/2.94  thf('42', plain,
% 2.73/2.94      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.73/2.94      inference('split', [status(esa)], ['8'])).
% 2.73/2.94  thf('43', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.73/2.94      inference('sup-', [status(thm)], ['41', '42'])).
% 2.73/2.94  thf('44', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.73/2.94      inference('split', [status(esa)], ['8'])).
% 2.73/2.94  thf('45', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.73/2.94      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 2.73/2.94  thf('46', plain, (~ (v2_funct_1 @ sk_C)),
% 2.73/2.94      inference('simpl_trail', [status(thm)], ['9', '45'])).
% 2.73/2.94  thf('47', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.73/2.94      inference('sup-', [status(thm)], ['7', '46'])).
% 2.73/2.94  thf('48', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('49', plain,
% 2.73/2.94      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.73/2.94         (~ (v1_xboole_0 @ X10)
% 2.73/2.94          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 2.73/2.94          | (v1_xboole_0 @ X11))),
% 2.73/2.94      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.73/2.94  thf('50', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.73/2.94      inference('sup-', [status(thm)], ['48', '49'])).
% 2.73/2.94  thf('51', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('52', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k1_partfun1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ E ) & 
% 2.73/2.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( v1_funct_1 @ F ) & 
% 2.73/2.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.94       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.73/2.94  thf('53', plain,
% 2.73/2.94      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.73/2.94          | ~ (v1_funct_1 @ X35)
% 2.73/2.94          | ~ (v1_funct_1 @ X38)
% 2.73/2.94          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.73/2.94          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 2.73/2.94              = (k5_relat_1 @ X35 @ X38)))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.73/2.94  thf('54', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.73/2.94          | ~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['52', '53'])).
% 2.73/2.94  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('56', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.73/2.94          | ~ (v1_funct_1 @ X0))),
% 2.73/2.94      inference('demod', [status(thm)], ['54', '55'])).
% 2.73/2.94  thf('57', plain,
% 2.73/2.94      ((~ (v1_funct_1 @ sk_D)
% 2.73/2.94        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['51', '56'])).
% 2.73/2.94  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('59', plain,
% 2.73/2.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['57', '58'])).
% 2.73/2.94  thf('60', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(t26_funct_2, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ![E:$i]:
% 2.73/2.94         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.73/2.94             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.73/2.94           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.73/2.94             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.73/2.94               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.73/2.94  thf('61', plain,
% 2.73/2.94      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X46)
% 2.73/2.94          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 2.73/2.94          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 2.73/2.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46))
% 2.73/2.94          | (v2_funct_1 @ X50)
% 2.73/2.94          | ((X48) = (k1_xboole_0))
% 2.73/2.94          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 2.73/2.94          | ~ (v1_funct_2 @ X50 @ X49 @ X47)
% 2.73/2.94          | ~ (v1_funct_1 @ X50))),
% 2.73/2.94      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.73/2.94  thf('62', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.73/2.94          | ((sk_A) = (k1_xboole_0))
% 2.73/2.94          | (v2_funct_1 @ X0)
% 2.73/2.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.73/2.94          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['60', '61'])).
% 2.73/2.94  thf('63', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('65', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.73/2.94          | ((sk_A) = (k1_xboole_0))
% 2.73/2.94          | (v2_funct_1 @ X0)
% 2.73/2.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.73/2.94      inference('demod', [status(thm)], ['62', '63', '64'])).
% 2.73/2.94  thf('66', plain,
% 2.73/2.94      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.73/2.94        | (v2_funct_1 @ sk_C)
% 2.73/2.94        | ((sk_A) = (k1_xboole_0))
% 2.73/2.94        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.73/2.94        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['59', '65'])).
% 2.73/2.94  thf('67', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('70', plain,
% 2.73/2.94      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.73/2.94        | (v2_funct_1 @ sk_C)
% 2.73/2.94        | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.94      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 2.73/2.94  thf('71', plain, (~ (v2_funct_1 @ sk_C)),
% 2.73/2.94      inference('simpl_trail', [status(thm)], ['9', '45'])).
% 2.73/2.94  thf('72', plain,
% 2.73/2.94      ((((sk_A) = (k1_xboole_0)) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 2.73/2.94      inference('clc', [status(thm)], ['70', '71'])).
% 2.73/2.94  thf('73', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['10', '11'])).
% 2.73/2.94  thf('74', plain,
% 2.73/2.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['57', '58'])).
% 2.73/2.94  thf('75', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['73', '74'])).
% 2.73/2.94  thf('76', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('77', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(dt_k4_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.94     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.94       ( m1_subset_1 @
% 2.73/2.94         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.73/2.94         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.73/2.94  thf('78', plain,
% 2.73/2.94      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 2.73/2.94          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.73/2.94          | (m1_subset_1 @ (k4_relset_1 @ X14 @ X15 @ X17 @ X18 @ X13 @ X16) @ 
% 2.73/2.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X18))))),
% 2.73/2.94      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.73/2.94  thf('79', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.73/2.94      inference('sup-', [status(thm)], ['77', '78'])).
% 2.73/2.94  thf('80', plain,
% 2.73/2.94      ((m1_subset_1 @ 
% 2.73/2.94        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['76', '79'])).
% 2.73/2.94  thf('81', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('82', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k4_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.94     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.94       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.73/2.94  thf('83', plain,
% 2.73/2.94      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.73/2.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.73/2.94          | ((k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 2.73/2.94              = (k5_relat_1 @ X22 @ X25)))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.73/2.94  thf('84', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.73/2.94      inference('sup-', [status(thm)], ['82', '83'])).
% 2.73/2.94  thf('85', plain,
% 2.73/2.94      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['81', '84'])).
% 2.73/2.94  thf('86', plain,
% 2.73/2.94      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.73/2.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.73/2.94      inference('demod', [status(thm)], ['80', '85'])).
% 2.73/2.94  thf(redefinition_r2_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.94     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.73/2.94  thf('87', plain,
% 2.73/2.94      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.73/2.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.73/2.94          | ((X28) = (X31))
% 2.73/2.94          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.73/2.94  thf('88', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.73/2.94          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.94      inference('sup-', [status(thm)], ['86', '87'])).
% 2.73/2.94  thf('89', plain,
% 2.73/2.94      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.73/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.73/2.94        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['75', '88'])).
% 2.73/2.94  thf('90', plain,
% 2.73/2.94      (![X32 : $i]:
% 2.73/2.94         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 2.73/2.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 2.73/2.94      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.73/2.94  thf('91', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['89', '90'])).
% 2.73/2.94  thf('92', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.73/2.94      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.73/2.94  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 2.73/2.94      inference('demod', [status(thm)], ['72', '91', '92'])).
% 2.73/2.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.73/2.94  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.73/2.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.73/2.94  thf('95', plain, ((v1_xboole_0 @ sk_C)),
% 2.73/2.94      inference('demod', [status(thm)], ['50', '93', '94'])).
% 2.73/2.94  thf('96', plain, ($false), inference('demod', [status(thm)], ['47', '95'])).
% 2.73/2.94  
% 2.73/2.94  % SZS output end Refutation
% 2.73/2.94  
% 2.73/2.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
