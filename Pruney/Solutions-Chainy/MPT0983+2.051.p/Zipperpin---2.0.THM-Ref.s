%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ePxEZsPkB3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:09 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 328 expanded)
%              Number of leaves         :   37 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          : 1094 (6592 expanded)
%              Number of equality atoms :   34 (  81 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('9',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( r2_relset_1 @ X29 @ X29 @ ( k1_partfun1 @ X29 @ X30 @ X30 @ X29 @ X28 @ X31 ) @ ( k6_partfun1 @ X29 ) )
      | ( ( k2_relset_1 @ X30 @ X29 @ X31 )
        = X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('19',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( r2_relset_1 @ X29 @ X29 @ ( k1_partfun1 @ X29 @ X30 @ X30 @ X29 @ X28 @ X31 ) @ ( k6_relat_1 @ X29 ) )
      | ( ( k2_relset_1 @ X30 @ X29 @ X31 )
        = X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','28','29','30','31'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != X19 )
      | ( v2_funct_2 @ X20 @ X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('34',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v5_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
      | ( v2_funct_2 @ X20 @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','28','29','30','31'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['35','38','39','42'])).

thf('44',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('45',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('47',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('66',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X35 @ X33 @ X33 @ X34 @ X36 @ X32 ) )
      | ( v2_funct_1 @ X36 )
      | ( X34 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X33 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('80',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['78','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['51','82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['48','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ePxEZsPkB3
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.35/3.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.35/3.57  % Solved by: fo/fo7.sh
% 3.35/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.35/3.57  % done 2644 iterations in 3.115s
% 3.35/3.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.35/3.57  % SZS output start Refutation
% 3.35/3.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.35/3.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.35/3.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.35/3.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.35/3.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.35/3.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.35/3.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.35/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.35/3.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.35/3.57  thf(sk_B_type, type, sk_B: $i).
% 3.35/3.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.35/3.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.35/3.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.35/3.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.35/3.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.35/3.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.35/3.57  thf(sk_C_type, type, sk_C: $i).
% 3.35/3.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.35/3.57  thf(sk_D_type, type, sk_D: $i).
% 3.35/3.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.35/3.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.35/3.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.35/3.57  thf(l13_xboole_0, axiom,
% 3.35/3.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.35/3.57  thf('0', plain,
% 3.35/3.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.35/3.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.35/3.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.35/3.57  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.35/3.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.35/3.57  thf(t29_relset_1, axiom,
% 3.35/3.57    (![A:$i]:
% 3.35/3.57     ( m1_subset_1 @
% 3.35/3.57       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.35/3.57  thf('2', plain,
% 3.35/3.57      (![X18 : $i]:
% 3.35/3.57         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 3.35/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 3.35/3.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.35/3.57  thf(cc3_relset_1, axiom,
% 3.35/3.57    (![A:$i,B:$i]:
% 3.35/3.57     ( ( v1_xboole_0 @ A ) =>
% 3.35/3.57       ( ![C:$i]:
% 3.35/3.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.35/3.57           ( v1_xboole_0 @ C ) ) ) ))).
% 3.35/3.57  thf('3', plain,
% 3.35/3.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.35/3.57         (~ (v1_xboole_0 @ X8)
% 3.35/3.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 3.35/3.57          | (v1_xboole_0 @ X9))),
% 3.35/3.57      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.35/3.57  thf('4', plain,
% 3.35/3.57      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.35/3.57      inference('sup-', [status(thm)], ['2', '3'])).
% 3.35/3.57  thf('5', plain,
% 3.35/3.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.35/3.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.35/3.57  thf('6', plain,
% 3.35/3.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 3.35/3.57      inference('sup-', [status(thm)], ['4', '5'])).
% 3.35/3.57  thf('7', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.35/3.57      inference('sup-', [status(thm)], ['1', '6'])).
% 3.35/3.57  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.35/3.57  thf('8', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 3.35/3.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.35/3.57  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.35/3.57      inference('sup+', [status(thm)], ['7', '8'])).
% 3.35/3.57  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.35/3.57      inference('sup+', [status(thm)], ['0', '9'])).
% 3.35/3.57  thf(t29_funct_2, conjecture,
% 3.35/3.57    (![A:$i,B:$i,C:$i]:
% 3.35/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.35/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.35/3.57       ( ![D:$i]:
% 3.35/3.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.35/3.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.35/3.57           ( ( r2_relset_1 @
% 3.35/3.57               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.35/3.57               ( k6_partfun1 @ A ) ) =>
% 3.35/3.57             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.35/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.35/3.57    (~( ![A:$i,B:$i,C:$i]:
% 3.35/3.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.35/3.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.35/3.57          ( ![D:$i]:
% 3.35/3.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.35/3.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.35/3.57              ( ( r2_relset_1 @
% 3.35/3.57                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.35/3.57                  ( k6_partfun1 @ A ) ) =>
% 3.35/3.57                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.35/3.57    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.35/3.57  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.35/3.57      inference('split', [status(esa)], ['11'])).
% 3.35/3.57  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.35/3.57      inference('sup-', [status(thm)], ['10', '12'])).
% 3.35/3.57  thf('14', plain,
% 3.35/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.35/3.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.35/3.57        (k6_partfun1 @ sk_A))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(redefinition_k6_partfun1, axiom,
% 3.35/3.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.35/3.57  thf('15', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 3.35/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.35/3.57  thf('16', plain,
% 3.35/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.35/3.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.35/3.57        (k6_relat_1 @ sk_A))),
% 3.35/3.57      inference('demod', [status(thm)], ['14', '15'])).
% 3.35/3.57  thf('17', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(t24_funct_2, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i]:
% 3.35/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.35/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.35/3.57       ( ![D:$i]:
% 3.35/3.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.35/3.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.35/3.57           ( ( r2_relset_1 @
% 3.35/3.57               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.35/3.57               ( k6_partfun1 @ B ) ) =>
% 3.35/3.57             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.35/3.57  thf('18', plain,
% 3.35/3.57      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X28)
% 3.35/3.57          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 3.35/3.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.35/3.57          | ~ (r2_relset_1 @ X29 @ X29 @ 
% 3.35/3.57               (k1_partfun1 @ X29 @ X30 @ X30 @ X29 @ X28 @ X31) @ 
% 3.35/3.57               (k6_partfun1 @ X29))
% 3.35/3.57          | ((k2_relset_1 @ X30 @ X29 @ X31) = (X29))
% 3.35/3.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 3.35/3.57          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 3.35/3.57          | ~ (v1_funct_1 @ X31))),
% 3.35/3.57      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.35/3.57  thf('19', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 3.35/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.35/3.57  thf('20', plain,
% 3.35/3.57      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X28)
% 3.35/3.57          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 3.35/3.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.35/3.57          | ~ (r2_relset_1 @ X29 @ X29 @ 
% 3.35/3.57               (k1_partfun1 @ X29 @ X30 @ X30 @ X29 @ X28 @ X31) @ 
% 3.35/3.57               (k6_relat_1 @ X29))
% 3.35/3.57          | ((k2_relset_1 @ X30 @ X29 @ X31) = (X29))
% 3.35/3.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 3.35/3.57          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 3.35/3.57          | ~ (v1_funct_1 @ X31))),
% 3.35/3.57      inference('demod', [status(thm)], ['18', '19'])).
% 3.35/3.57  thf('21', plain,
% 3.35/3.57      (![X0 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X0)
% 3.35/3.57          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.35/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.35/3.57          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.35/3.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.35/3.57               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.35/3.57               (k6_relat_1 @ sk_A))
% 3.35/3.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.35/3.57          | ~ (v1_funct_1 @ sk_C))),
% 3.35/3.57      inference('sup-', [status(thm)], ['17', '20'])).
% 3.35/3.57  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('24', plain,
% 3.35/3.57      (![X0 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X0)
% 3.35/3.57          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.35/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.35/3.57          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.35/3.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.35/3.57               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.35/3.57               (k6_relat_1 @ sk_A)))),
% 3.35/3.57      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.35/3.57  thf('25', plain,
% 3.35/3.57      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.35/3.57        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.35/3.57        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.35/3.57        | ~ (v1_funct_1 @ sk_D))),
% 3.35/3.57      inference('sup-', [status(thm)], ['16', '24'])).
% 3.35/3.57  thf('26', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(redefinition_k2_relset_1, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i]:
% 3.35/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.35/3.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.35/3.57  thf('27', plain,
% 3.35/3.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.35/3.57         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 3.35/3.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.35/3.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.35/3.57  thf('28', plain,
% 3.35/3.57      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.35/3.57      inference('sup-', [status(thm)], ['26', '27'])).
% 3.35/3.57  thf('29', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('32', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.35/3.57      inference('demod', [status(thm)], ['25', '28', '29', '30', '31'])).
% 3.35/3.57  thf(d3_funct_2, axiom,
% 3.35/3.57    (![A:$i,B:$i]:
% 3.35/3.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.35/3.57       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.35/3.57  thf('33', plain,
% 3.35/3.57      (![X19 : $i, X20 : $i]:
% 3.35/3.57         (((k2_relat_1 @ X20) != (X19))
% 3.35/3.57          | (v2_funct_2 @ X20 @ X19)
% 3.35/3.57          | ~ (v5_relat_1 @ X20 @ X19)
% 3.35/3.57          | ~ (v1_relat_1 @ X20))),
% 3.35/3.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.35/3.57  thf('34', plain,
% 3.35/3.57      (![X20 : $i]:
% 3.35/3.57         (~ (v1_relat_1 @ X20)
% 3.35/3.57          | ~ (v5_relat_1 @ X20 @ (k2_relat_1 @ X20))
% 3.35/3.57          | (v2_funct_2 @ X20 @ (k2_relat_1 @ X20)))),
% 3.35/3.57      inference('simplify', [status(thm)], ['33'])).
% 3.35/3.57  thf('35', plain,
% 3.35/3.57      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.35/3.57        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.35/3.57        | ~ (v1_relat_1 @ sk_D))),
% 3.35/3.57      inference('sup-', [status(thm)], ['32', '34'])).
% 3.35/3.57  thf('36', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(cc2_relset_1, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i]:
% 3.35/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.35/3.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.35/3.57  thf('37', plain,
% 3.35/3.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.35/3.57         ((v5_relat_1 @ X5 @ X7)
% 3.35/3.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.35/3.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.35/3.57  thf('38', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.35/3.57      inference('sup-', [status(thm)], ['36', '37'])).
% 3.35/3.57  thf('39', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.35/3.57      inference('demod', [status(thm)], ['25', '28', '29', '30', '31'])).
% 3.35/3.57  thf('40', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(cc1_relset_1, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i]:
% 3.35/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.35/3.57       ( v1_relat_1 @ C ) ))).
% 3.35/3.57  thf('41', plain,
% 3.35/3.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.35/3.57         ((v1_relat_1 @ X2)
% 3.35/3.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 3.35/3.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.35/3.57  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 3.35/3.57      inference('sup-', [status(thm)], ['40', '41'])).
% 3.35/3.57  thf('43', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.35/3.57      inference('demod', [status(thm)], ['35', '38', '39', '42'])).
% 3.35/3.57  thf('44', plain,
% 3.35/3.57      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.35/3.57      inference('split', [status(esa)], ['11'])).
% 3.35/3.57  thf('45', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.35/3.57      inference('sup-', [status(thm)], ['43', '44'])).
% 3.35/3.57  thf('46', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.35/3.57      inference('split', [status(esa)], ['11'])).
% 3.35/3.57  thf('47', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.35/3.57      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 3.35/3.57  thf('48', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.35/3.57      inference('simpl_trail', [status(thm)], ['13', '47'])).
% 3.35/3.57  thf('49', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('50', plain,
% 3.35/3.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.35/3.57         (~ (v1_xboole_0 @ X8)
% 3.35/3.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 3.35/3.57          | (v1_xboole_0 @ X9))),
% 3.35/3.57      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.35/3.57  thf('51', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.35/3.57      inference('sup-', [status(thm)], ['49', '50'])).
% 3.35/3.57  thf('52', plain,
% 3.35/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.35/3.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.35/3.57        (k6_relat_1 @ sk_A))),
% 3.35/3.57      inference('demod', [status(thm)], ['14', '15'])).
% 3.35/3.57  thf('53', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('54', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(dt_k1_partfun1, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.35/3.57     ( ( ( v1_funct_1 @ E ) & 
% 3.35/3.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.35/3.57         ( v1_funct_1 @ F ) & 
% 3.35/3.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.35/3.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.35/3.57         ( m1_subset_1 @
% 3.35/3.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.35/3.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.35/3.57  thf('55', plain,
% 3.35/3.57      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.35/3.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.35/3.57          | ~ (v1_funct_1 @ X21)
% 3.35/3.57          | ~ (v1_funct_1 @ X24)
% 3.35/3.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.35/3.57          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 3.35/3.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 3.35/3.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.35/3.57  thf('56', plain,
% 3.35/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.35/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.35/3.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.35/3.57          | ~ (v1_funct_1 @ X1)
% 3.35/3.57          | ~ (v1_funct_1 @ sk_C))),
% 3.35/3.57      inference('sup-', [status(thm)], ['54', '55'])).
% 3.35/3.57  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('58', plain,
% 3.35/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.35/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.35/3.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.35/3.57          | ~ (v1_funct_1 @ X1))),
% 3.35/3.57      inference('demod', [status(thm)], ['56', '57'])).
% 3.35/3.57  thf('59', plain,
% 3.35/3.57      ((~ (v1_funct_1 @ sk_D)
% 3.35/3.57        | (m1_subset_1 @ 
% 3.35/3.57           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.35/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.35/3.57      inference('sup-', [status(thm)], ['53', '58'])).
% 3.35/3.57  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('61', plain,
% 3.35/3.57      ((m1_subset_1 @ 
% 3.35/3.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.35/3.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.35/3.57      inference('demod', [status(thm)], ['59', '60'])).
% 3.35/3.57  thf(redefinition_r2_relset_1, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.35/3.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.35/3.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.35/3.57  thf('62', plain,
% 3.35/3.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 3.35/3.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 3.35/3.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 3.35/3.57          | ((X14) = (X17))
% 3.35/3.57          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 3.35/3.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.35/3.57  thf('63', plain,
% 3.35/3.57      (![X0 : $i]:
% 3.35/3.57         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.35/3.57             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.35/3.57          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.35/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.35/3.57      inference('sup-', [status(thm)], ['61', '62'])).
% 3.35/3.57  thf('64', plain,
% 3.35/3.57      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.35/3.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.35/3.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.35/3.57            = (k6_relat_1 @ sk_A)))),
% 3.35/3.57      inference('sup-', [status(thm)], ['52', '63'])).
% 3.35/3.57  thf('65', plain,
% 3.35/3.57      (![X18 : $i]:
% 3.35/3.57         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 3.35/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 3.35/3.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.35/3.57  thf('66', plain,
% 3.35/3.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.35/3.57         = (k6_relat_1 @ sk_A))),
% 3.35/3.57      inference('demod', [status(thm)], ['64', '65'])).
% 3.35/3.57  thf('67', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf(t26_funct_2, axiom,
% 3.35/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.35/3.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.35/3.57       ( ![E:$i]:
% 3.35/3.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.35/3.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.35/3.57           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.35/3.57             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.35/3.57               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.35/3.57  thf('68', plain,
% 3.35/3.57      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X32)
% 3.35/3.57          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 3.35/3.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.35/3.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X35 @ X33 @ X33 @ X34 @ X36 @ X32))
% 3.35/3.57          | (v2_funct_1 @ X36)
% 3.35/3.57          | ((X34) = (k1_xboole_0))
% 3.35/3.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 3.35/3.57          | ~ (v1_funct_2 @ X36 @ X35 @ X33)
% 3.35/3.57          | ~ (v1_funct_1 @ X36))),
% 3.35/3.57      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.35/3.57  thf('69', plain,
% 3.35/3.57      (![X0 : $i, X1 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X0)
% 3.35/3.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.35/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.35/3.57          | ((sk_A) = (k1_xboole_0))
% 3.35/3.57          | (v2_funct_1 @ X0)
% 3.35/3.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.35/3.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.35/3.57          | ~ (v1_funct_1 @ sk_D))),
% 3.35/3.57      inference('sup-', [status(thm)], ['67', '68'])).
% 3.35/3.57  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('72', plain,
% 3.35/3.57      (![X0 : $i, X1 : $i]:
% 3.35/3.57         (~ (v1_funct_1 @ X0)
% 3.35/3.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.35/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.35/3.57          | ((sk_A) = (k1_xboole_0))
% 3.35/3.57          | (v2_funct_1 @ X0)
% 3.35/3.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.35/3.57      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.35/3.57  thf('73', plain,
% 3.35/3.57      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.35/3.57        | (v2_funct_1 @ sk_C)
% 3.35/3.57        | ((sk_A) = (k1_xboole_0))
% 3.35/3.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.35/3.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.35/3.57        | ~ (v1_funct_1 @ sk_C))),
% 3.35/3.57      inference('sup-', [status(thm)], ['66', '72'])).
% 3.35/3.57  thf('74', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 3.35/3.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.35/3.57  thf('75', plain,
% 3.35/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 3.35/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.57  thf('78', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.35/3.57      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 3.35/3.57  thf('79', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.35/3.57      inference('split', [status(esa)], ['11'])).
% 3.35/3.57  thf('80', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.35/3.57      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 3.35/3.57  thf('81', plain, (~ (v2_funct_1 @ sk_C)),
% 3.35/3.57      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 3.35/3.57  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 3.35/3.57      inference('clc', [status(thm)], ['78', '81'])).
% 3.35/3.57  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.35/3.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.35/3.57  thf('84', plain, ((v1_xboole_0 @ sk_C)),
% 3.35/3.57      inference('demod', [status(thm)], ['51', '82', '83'])).
% 3.35/3.57  thf('85', plain, ($false), inference('demod', [status(thm)], ['48', '84'])).
% 3.35/3.57  
% 3.35/3.57  % SZS output end Refutation
% 3.35/3.57  
% 3.35/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
