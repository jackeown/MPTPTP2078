%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZqTaSZyFPU

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:08 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 313 expanded)
%              Number of leaves         :   37 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          : 1053 (6340 expanded)
%              Number of equality atoms :   33 (  67 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','8'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('11',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

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

thf('15',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_partfun1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != X20 )
      | ( v2_funct_2 @ X21 @ X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('34',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
      | ( v2_funct_2 @ X21 @ ( k2_relat_1 @ X21 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
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
    inference(split,[status(esa)],['15'])).

thf('45',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('47',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['17','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('66',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33 ) )
      | ( v2_funct_1 @ X37 )
      | ( X35 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X34 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
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
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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
    inference(split,[status(esa)],['15'])).

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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZqTaSZyFPU
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.44/2.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.44/2.66  % Solved by: fo/fo7.sh
% 2.44/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.44/2.66  % done 2166 iterations in 2.208s
% 2.44/2.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.44/2.66  % SZS output start Refutation
% 2.44/2.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.44/2.66  thf(sk_D_type, type, sk_D: $i).
% 2.44/2.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.44/2.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.44/2.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.44/2.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.44/2.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.44/2.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.44/2.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.44/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.44/2.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.44/2.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.44/2.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.44/2.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.44/2.66  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.44/2.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.44/2.66  thf(sk_B_type, type, sk_B: $i).
% 2.44/2.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.44/2.66  thf(sk_C_type, type, sk_C: $i).
% 2.44/2.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.44/2.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.44/2.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.44/2.66  thf(l13_xboole_0, axiom,
% 2.44/2.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.44/2.66  thf('0', plain,
% 2.44/2.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.44/2.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.44/2.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.44/2.66  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.44/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.44/2.66  thf(t29_relset_1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( m1_subset_1 @
% 2.44/2.66       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.44/2.66  thf('2', plain,
% 2.44/2.66      (![X19 : $i]:
% 2.44/2.66         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 2.44/2.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 2.44/2.66      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.44/2.66  thf(redefinition_k6_partfun1, axiom,
% 2.44/2.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.44/2.66  thf('3', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.44/2.66  thf('4', plain,
% 2.44/2.66      (![X19 : $i]:
% 2.44/2.66         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 2.44/2.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 2.44/2.66      inference('demod', [status(thm)], ['2', '3'])).
% 2.44/2.66  thf(cc3_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i]:
% 2.44/2.66     ( ( v1_xboole_0 @ A ) =>
% 2.44/2.66       ( ![C:$i]:
% 2.44/2.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66           ( v1_xboole_0 @ C ) ) ) ))).
% 2.44/2.66  thf('5', plain,
% 2.44/2.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.44/2.66         (~ (v1_xboole_0 @ X9)
% 2.44/2.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 2.44/2.66          | (v1_xboole_0 @ X10))),
% 2.44/2.66      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.44/2.66  thf('6', plain,
% 2.44/2.66      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.44/2.66      inference('sup-', [status(thm)], ['4', '5'])).
% 2.44/2.66  thf('7', plain,
% 2.44/2.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.44/2.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.44/2.66  thf('8', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (~ (v1_xboole_0 @ X0) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.44/2.66  thf('9', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.44/2.66      inference('sup-', [status(thm)], ['1', '8'])).
% 2.44/2.66  thf(fc4_funct_1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.44/2.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.44/2.66  thf('10', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 2.44/2.66      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.44/2.66  thf('11', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.44/2.66  thf('12', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 2.44/2.66      inference('demod', [status(thm)], ['10', '11'])).
% 2.44/2.66  thf('13', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.44/2.66      inference('sup+', [status(thm)], ['9', '12'])).
% 2.44/2.66  thf('14', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.44/2.66      inference('sup+', [status(thm)], ['0', '13'])).
% 2.44/2.66  thf(t29_funct_2, conjecture,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.44/2.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ![D:$i]:
% 2.44/2.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.44/2.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.44/2.66           ( ( r2_relset_1 @
% 2.44/2.66               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.44/2.66               ( k6_partfun1 @ A ) ) =>
% 2.44/2.66             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.44/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.44/2.66    (~( ![A:$i,B:$i,C:$i]:
% 2.44/2.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.44/2.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66          ( ![D:$i]:
% 2.44/2.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.44/2.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.44/2.66              ( ( r2_relset_1 @
% 2.44/2.66                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.44/2.66                  ( k6_partfun1 @ A ) ) =>
% 2.44/2.66                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.44/2.66    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.44/2.66  thf('15', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('16', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.44/2.66      inference('split', [status(esa)], ['15'])).
% 2.44/2.66  thf('17', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['14', '16'])).
% 2.44/2.66  thf('18', plain,
% 2.44/2.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66        (k6_partfun1 @ sk_A))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('19', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(t24_funct_2, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.44/2.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ![D:$i]:
% 2.44/2.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.44/2.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.44/2.66           ( ( r2_relset_1 @
% 2.44/2.66               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.44/2.66               ( k6_partfun1 @ B ) ) =>
% 2.44/2.66             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.44/2.66  thf('20', plain,
% 2.44/2.66      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.44/2.66         (~ (v1_funct_1 @ X29)
% 2.44/2.66          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 2.44/2.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.44/2.66          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 2.44/2.66               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 2.44/2.66               (k6_partfun1 @ X30))
% 2.44/2.66          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 2.44/2.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 2.44/2.66          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 2.44/2.66          | ~ (v1_funct_1 @ X32))),
% 2.44/2.66      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.44/2.66  thf('21', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.44/2.66          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.44/2.66          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.44/2.66               (k6_partfun1 @ sk_A))
% 2.44/2.66          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.44/2.66          | ~ (v1_funct_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['19', '20'])).
% 2.44/2.66  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('24', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.44/2.66          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.44/2.66          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.44/2.66               (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.44/2.66  thf('25', plain,
% 2.44/2.66      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.44/2.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.44/2.66        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.44/2.66        | ~ (v1_funct_1 @ sk_D))),
% 2.44/2.66      inference('sup-', [status(thm)], ['18', '24'])).
% 2.44/2.66  thf('26', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(redefinition_k2_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.44/2.66  thf('27', plain,
% 2.44/2.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.44/2.66         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 2.44/2.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.44/2.66  thf('28', plain,
% 2.44/2.66      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.44/2.66      inference('sup-', [status(thm)], ['26', '27'])).
% 2.44/2.66  thf('29', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('32', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.44/2.66      inference('demod', [status(thm)], ['25', '28', '29', '30', '31'])).
% 2.44/2.66  thf(d3_funct_2, axiom,
% 2.44/2.66    (![A:$i,B:$i]:
% 2.44/2.66     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.44/2.66       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.44/2.66  thf('33', plain,
% 2.44/2.66      (![X20 : $i, X21 : $i]:
% 2.44/2.66         (((k2_relat_1 @ X21) != (X20))
% 2.44/2.66          | (v2_funct_2 @ X21 @ X20)
% 2.44/2.66          | ~ (v5_relat_1 @ X21 @ X20)
% 2.44/2.66          | ~ (v1_relat_1 @ X21))),
% 2.44/2.66      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.44/2.66  thf('34', plain,
% 2.44/2.66      (![X21 : $i]:
% 2.44/2.66         (~ (v1_relat_1 @ X21)
% 2.44/2.66          | ~ (v5_relat_1 @ X21 @ (k2_relat_1 @ X21))
% 2.44/2.66          | (v2_funct_2 @ X21 @ (k2_relat_1 @ X21)))),
% 2.44/2.66      inference('simplify', [status(thm)], ['33'])).
% 2.44/2.66  thf('35', plain,
% 2.44/2.66      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.44/2.66        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.44/2.66        | ~ (v1_relat_1 @ sk_D))),
% 2.44/2.66      inference('sup-', [status(thm)], ['32', '34'])).
% 2.44/2.66  thf('36', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(cc2_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.44/2.66  thf('37', plain,
% 2.44/2.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.44/2.66         ((v5_relat_1 @ X6 @ X8)
% 2.44/2.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.44/2.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.44/2.66  thf('38', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.44/2.66      inference('sup-', [status(thm)], ['36', '37'])).
% 2.44/2.66  thf('39', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.44/2.66      inference('demod', [status(thm)], ['25', '28', '29', '30', '31'])).
% 2.44/2.66  thf('40', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(cc1_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66       ( v1_relat_1 @ C ) ))).
% 2.44/2.66  thf('41', plain,
% 2.44/2.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.44/2.66         ((v1_relat_1 @ X3)
% 2.44/2.66          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.44/2.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.44/2.66  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 2.44/2.66      inference('sup-', [status(thm)], ['40', '41'])).
% 2.44/2.66  thf('43', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.44/2.66      inference('demod', [status(thm)], ['35', '38', '39', '42'])).
% 2.44/2.66  thf('44', plain,
% 2.44/2.66      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.44/2.66      inference('split', [status(esa)], ['15'])).
% 2.44/2.66  thf('45', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.44/2.66      inference('sup-', [status(thm)], ['43', '44'])).
% 2.44/2.66  thf('46', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.44/2.66      inference('split', [status(esa)], ['15'])).
% 2.44/2.66  thf('47', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.44/2.66      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 2.44/2.66  thf('48', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.44/2.66      inference('simpl_trail', [status(thm)], ['17', '47'])).
% 2.44/2.66  thf('49', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('50', plain,
% 2.44/2.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.44/2.66         (~ (v1_xboole_0 @ X9)
% 2.44/2.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 2.44/2.66          | (v1_xboole_0 @ X10))),
% 2.44/2.66      inference('cnf', [status(esa)], [cc3_relset_1])).
% 2.44/2.66  thf('51', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.44/2.66      inference('sup-', [status(thm)], ['49', '50'])).
% 2.44/2.66  thf('52', plain,
% 2.44/2.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66        (k6_partfun1 @ sk_A))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('53', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('54', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(dt_k1_partfun1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ E ) & 
% 2.44/2.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.44/2.66         ( v1_funct_1 @ F ) & 
% 2.44/2.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.44/2.66       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.44/2.66         ( m1_subset_1 @
% 2.44/2.66           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.44/2.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.44/2.66  thf('55', plain,
% 2.44/2.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.44/2.66          | ~ (v1_funct_1 @ X22)
% 2.44/2.66          | ~ (v1_funct_1 @ X25)
% 2.44/2.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.44/2.66          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 2.44/2.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 2.44/2.66      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.44/2.66  thf('56', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.44/2.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.44/2.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.44/2.66          | ~ (v1_funct_1 @ X1)
% 2.44/2.66          | ~ (v1_funct_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['54', '55'])).
% 2.44/2.66  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('58', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.44/2.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.44/2.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.44/2.66          | ~ (v1_funct_1 @ X1))),
% 2.44/2.66      inference('demod', [status(thm)], ['56', '57'])).
% 2.44/2.66  thf('59', plain,
% 2.44/2.66      ((~ (v1_funct_1 @ sk_D)
% 2.44/2.66        | (m1_subset_1 @ 
% 2.44/2.66           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.44/2.66      inference('sup-', [status(thm)], ['53', '58'])).
% 2.44/2.66  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('61', plain,
% 2.44/2.66      ((m1_subset_1 @ 
% 2.44/2.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.44/2.66      inference('demod', [status(thm)], ['59', '60'])).
% 2.44/2.66  thf(redefinition_r2_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.44/2.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.44/2.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.44/2.66  thf('62', plain,
% 2.44/2.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 2.44/2.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 2.44/2.66          | ((X15) = (X18))
% 2.44/2.66          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.44/2.66  thf('63', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.44/2.66          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.44/2.66      inference('sup-', [status(thm)], ['61', '62'])).
% 2.44/2.66  thf('64', plain,
% 2.44/2.66      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.44/2.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.44/2.66            = (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['52', '63'])).
% 2.44/2.66  thf('65', plain,
% 2.44/2.66      (![X19 : $i]:
% 2.44/2.66         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 2.44/2.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 2.44/2.66      inference('demod', [status(thm)], ['2', '3'])).
% 2.44/2.66  thf('66', plain,
% 2.44/2.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.44/2.66         = (k6_partfun1 @ sk_A))),
% 2.44/2.66      inference('demod', [status(thm)], ['64', '65'])).
% 2.44/2.66  thf('67', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(t26_funct_2, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.44/2.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ![E:$i]:
% 2.44/2.66         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.44/2.66             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.44/2.66           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.44/2.66             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.44/2.66               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.44/2.66  thf('68', plain,
% 2.44/2.66      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.44/2.66         (~ (v1_funct_1 @ X33)
% 2.44/2.66          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.44/2.66          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.44/2.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33))
% 2.44/2.66          | (v2_funct_1 @ X37)
% 2.44/2.66          | ((X35) = (k1_xboole_0))
% 2.44/2.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 2.44/2.66          | ~ (v1_funct_2 @ X37 @ X36 @ X34)
% 2.44/2.66          | ~ (v1_funct_1 @ X37))),
% 2.44/2.66      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.44/2.66  thf('69', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i]:
% 2.44/2.66         (~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.44/2.66          | ((sk_A) = (k1_xboole_0))
% 2.44/2.66          | (v2_funct_1 @ X0)
% 2.44/2.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.44/2.66          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.44/2.66          | ~ (v1_funct_1 @ sk_D))),
% 2.44/2.66      inference('sup-', [status(thm)], ['67', '68'])).
% 2.44/2.66  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('72', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i]:
% 2.44/2.66         (~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.44/2.66          | ((sk_A) = (k1_xboole_0))
% 2.44/2.66          | (v2_funct_1 @ X0)
% 2.44/2.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.44/2.66      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.44/2.66  thf('73', plain,
% 2.44/2.66      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.44/2.66        | (v2_funct_1 @ sk_C)
% 2.44/2.66        | ((sk_A) = (k1_xboole_0))
% 2.44/2.66        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.44/2.66        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.44/2.66        | ~ (v1_funct_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['66', '72'])).
% 2.44/2.66  thf('74', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 2.44/2.66      inference('demod', [status(thm)], ['10', '11'])).
% 2.44/2.66  thf('75', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('78', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.44/2.66      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 2.44/2.66  thf('79', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.44/2.66      inference('split', [status(esa)], ['15'])).
% 2.44/2.66  thf('80', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.44/2.66      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 2.44/2.66  thf('81', plain, (~ (v2_funct_1 @ sk_C)),
% 2.44/2.66      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 2.44/2.66  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 2.44/2.66      inference('clc', [status(thm)], ['78', '81'])).
% 2.44/2.66  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.44/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.44/2.66  thf('84', plain, ((v1_xboole_0 @ sk_C)),
% 2.44/2.66      inference('demod', [status(thm)], ['51', '82', '83'])).
% 2.44/2.66  thf('85', plain, ($false), inference('demod', [status(thm)], ['48', '84'])).
% 2.44/2.66  
% 2.44/2.66  % SZS output end Refutation
% 2.44/2.66  
% 2.44/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
