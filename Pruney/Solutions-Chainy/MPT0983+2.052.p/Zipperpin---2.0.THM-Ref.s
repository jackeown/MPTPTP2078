%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HYfGWjBj7a

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:09 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 323 expanded)
%              Number of leaves         :   37 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          : 1093 (6584 expanded)
%              Number of equality atoms :   32 (  78 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
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
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
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

thf('10',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
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

thf('16',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_relat_1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != X20 )
      | ( v2_funct_2 @ X21 @ X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
      | ( v2_funct_2 @ X21 @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['32','35','36','39'])).

thf('41',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['10','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
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

thf('65',plain,(
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

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('77',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['75','78'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['48','79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['45','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HYfGWjBj7a
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 838 iterations in 0.750s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.00/1.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.00/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.00/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.20  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.00/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.00/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.00/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.00/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.00/1.20  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.00/1.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.00/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.00/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.00/1.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.00/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.20  thf(t29_relset_1, axiom,
% 1.00/1.20    (![A:$i]:
% 1.00/1.20     ( m1_subset_1 @
% 1.00/1.20       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      (![X19 : $i]:
% 1.00/1.20         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.00/1.20  thf(cc3_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( v1_xboole_0 @ A ) =>
% 1.00/1.20       ( ![C:$i]:
% 1.00/1.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20           ( v1_xboole_0 @ C ) ) ) ))).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.20         (~ (v1_xboole_0 @ X9)
% 1.00/1.20          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 1.00/1.20          | (v1_xboole_0 @ X10))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['0', '1'])).
% 1.00/1.20  thf(t8_boole, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t8_boole])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_xboole_0 @ X0)
% 1.00/1.20          | ((k6_relat_1 @ X0) = (X1))
% 1.00/1.20          | ~ (v1_xboole_0 @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.00/1.20  thf('5', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 1.00/1.20      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.00/1.20      inference('sup+', [status(thm)], ['4', '5'])).
% 1.00/1.20  thf('7', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.00/1.20      inference('condensation', [status(thm)], ['6'])).
% 1.00/1.20  thf(t29_funct_2, conjecture,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.00/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.00/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.00/1.20           ( ( r2_relset_1 @
% 1.00/1.20               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.00/1.20               ( k6_partfun1 @ A ) ) =>
% 1.00/1.20             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.00/1.20        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.00/1.20            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.00/1.20          ( ![D:$i]:
% 1.00/1.20            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.00/1.20                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.00/1.20              ( ( r2_relset_1 @
% 1.00/1.20                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.00/1.20                  ( k6_partfun1 @ A ) ) =>
% 1.00/1.20                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.00/1.20  thf('8', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('9', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.00/1.20      inference('split', [status(esa)], ['8'])).
% 1.00/1.20  thf('10', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['7', '9'])).
% 1.00/1.20  thf('11', plain,
% 1.00/1.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.00/1.20        (k6_partfun1 @ sk_A))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(redefinition_k6_partfun1, axiom,
% 1.00/1.20    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.00/1.20  thf('12', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.00/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.00/1.20        (k6_relat_1 @ sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['11', '12'])).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(t24_funct_2, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.00/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.00/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.00/1.20           ( ( r2_relset_1 @
% 1.00/1.20               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.00/1.20               ( k6_partfun1 @ B ) ) =>
% 1.00/1.20             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X29)
% 1.00/1.20          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 1.00/1.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.00/1.20          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 1.00/1.20               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 1.00/1.20               (k6_partfun1 @ X30))
% 1.00/1.20          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 1.00/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.00/1.20          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.00/1.20          | ~ (v1_funct_1 @ X32))),
% 1.00/1.20      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.00/1.20  thf('16', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.00/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.00/1.20  thf('17', plain,
% 1.00/1.20      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X29)
% 1.00/1.20          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 1.00/1.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.00/1.20          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 1.00/1.20               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 1.00/1.20               (k6_relat_1 @ X30))
% 1.00/1.20          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 1.00/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.00/1.20          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.00/1.20          | ~ (v1_funct_1 @ X32))),
% 1.00/1.20      inference('demod', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X0)
% 1.00/1.20          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.00/1.20          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.00/1.20          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.20               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.00/1.20               (k6_relat_1 @ sk_A))
% 1.00/1.20          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.00/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.00/1.20      inference('sup-', [status(thm)], ['14', '17'])).
% 1.00/1.20  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X0)
% 1.00/1.20          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.00/1.20          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.00/1.20          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.20               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.00/1.20               (k6_relat_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.00/1.20  thf('22', plain,
% 1.00/1.20      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.00/1.20        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.00/1.20        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.00/1.20        | ~ (v1_funct_1 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['13', '21'])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(redefinition_k2_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.00/1.20         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.00/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.00/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.00/1.20  thf('26', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.00/1.20  thf(d3_funct_2, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.00/1.20       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.00/1.20  thf('30', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i]:
% 1.00/1.20         (((k2_relat_1 @ X21) != (X20))
% 1.00/1.20          | (v2_funct_2 @ X21 @ X20)
% 1.00/1.20          | ~ (v5_relat_1 @ X21 @ X20)
% 1.00/1.20          | ~ (v1_relat_1 @ X21))),
% 1.00/1.20      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      (![X21 : $i]:
% 1.00/1.20         (~ (v1_relat_1 @ X21)
% 1.00/1.20          | ~ (v5_relat_1 @ X21 @ (k2_relat_1 @ X21))
% 1.00/1.20          | (v2_funct_2 @ X21 @ (k2_relat_1 @ X21)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['30'])).
% 1.00/1.20  thf('32', plain,
% 1.00/1.20      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.00/1.20        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.00/1.20        | ~ (v1_relat_1 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['29', '31'])).
% 1.00/1.20  thf('33', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(cc2_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.00/1.20  thf('34', plain,
% 1.00/1.20      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.20         ((v5_relat_1 @ X6 @ X8)
% 1.00/1.20          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.00/1.20  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.00/1.20  thf('37', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(cc1_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.20       ( v1_relat_1 @ C ) ))).
% 1.00/1.20  thf('38', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.00/1.20         ((v1_relat_1 @ X3)
% 1.00/1.20          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.00/1.20  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 1.00/1.20      inference('sup-', [status(thm)], ['37', '38'])).
% 1.00/1.20  thf('40', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.00/1.20      inference('demod', [status(thm)], ['32', '35', '36', '39'])).
% 1.00/1.20  thf('41', plain,
% 1.00/1.20      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.00/1.20      inference('split', [status(esa)], ['8'])).
% 1.00/1.20  thf('42', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.00/1.20      inference('sup-', [status(thm)], ['40', '41'])).
% 1.00/1.20  thf('43', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.00/1.20      inference('split', [status(esa)], ['8'])).
% 1.00/1.20  thf('44', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.00/1.20      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 1.00/1.20  thf('45', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.00/1.20      inference('simpl_trail', [status(thm)], ['10', '44'])).
% 1.00/1.20  thf('46', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('47', plain,
% 1.00/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.20         (~ (v1_xboole_0 @ X9)
% 1.00/1.20          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 1.00/1.20          | (v1_xboole_0 @ X10))),
% 1.00/1.20      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.00/1.20  thf('48', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.00/1.20      inference('sup-', [status(thm)], ['46', '47'])).
% 1.00/1.20  thf('49', plain,
% 1.00/1.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.00/1.20        (k6_relat_1 @ sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['11', '12'])).
% 1.00/1.20  thf('50', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('51', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(dt_k1_partfun1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.00/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.00/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.00/1.20         ( v1_funct_1 @ F ) & 
% 1.00/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.00/1.20       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.00/1.20         ( m1_subset_1 @
% 1.00/1.20           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.00/1.20           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.00/1.20  thf('52', plain,
% 1.00/1.20      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.00/1.20          | ~ (v1_funct_1 @ X22)
% 1.00/1.20          | ~ (v1_funct_1 @ X25)
% 1.00/1.20          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.00/1.20          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.00/1.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.00/1.20  thf('53', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.00/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.00/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.00/1.20          | ~ (v1_funct_1 @ X1)
% 1.00/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.00/1.20      inference('sup-', [status(thm)], ['51', '52'])).
% 1.00/1.20  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('55', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.00/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.00/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.00/1.20          | ~ (v1_funct_1 @ X1))),
% 1.00/1.20      inference('demod', [status(thm)], ['53', '54'])).
% 1.00/1.20  thf('56', plain,
% 1.00/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.00/1.20        | (m1_subset_1 @ 
% 1.00/1.20           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.00/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['50', '55'])).
% 1.00/1.20  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('58', plain,
% 1.00/1.20      ((m1_subset_1 @ 
% 1.00/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.00/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['56', '57'])).
% 1.00/1.20  thf(redefinition_r2_relset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.00/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.00/1.20       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.00/1.20  thf('59', plain,
% 1.00/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.00/1.20          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.00/1.20          | ((X15) = (X18))
% 1.00/1.20          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 1.00/1.20      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.00/1.20  thf('60', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.20             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.00/1.20          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['58', '59'])).
% 1.00/1.20  thf('61', plain,
% 1.00/1.20      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.00/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.00/1.20        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.00/1.20            = (k6_relat_1 @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['49', '60'])).
% 1.00/1.20  thf('62', plain,
% 1.00/1.20      (![X19 : $i]:
% 1.00/1.20         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 1.00/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.00/1.20  thf('63', plain,
% 1.00/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.00/1.20         = (k6_relat_1 @ sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['61', '62'])).
% 1.00/1.20  thf('64', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(t26_funct_2, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.00/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.00/1.20       ( ![E:$i]:
% 1.00/1.20         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.00/1.20             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.00/1.20           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.00/1.20             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.00/1.20               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.00/1.20  thf('65', plain,
% 1.00/1.20      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X33)
% 1.00/1.20          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 1.00/1.20          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.00/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X36 @ X34 @ X34 @ X35 @ X37 @ X33))
% 1.00/1.20          | (v2_funct_1 @ X37)
% 1.00/1.20          | ((X35) = (k1_xboole_0))
% 1.00/1.20          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 1.00/1.20          | ~ (v1_funct_2 @ X37 @ X36 @ X34)
% 1.00/1.20          | ~ (v1_funct_1 @ X37))),
% 1.00/1.20      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.00/1.20  thf('66', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X0)
% 1.00/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.00/1.20          | ((sk_A) = (k1_xboole_0))
% 1.00/1.20          | (v2_funct_1 @ X0)
% 1.00/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.00/1.20          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.00/1.20          | ~ (v1_funct_1 @ sk_D))),
% 1.00/1.20      inference('sup-', [status(thm)], ['64', '65'])).
% 1.00/1.20  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('69', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (v1_funct_1 @ X0)
% 1.00/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.00/1.20          | ((sk_A) = (k1_xboole_0))
% 1.00/1.20          | (v2_funct_1 @ X0)
% 1.00/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 1.00/1.20      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.00/1.20  thf('70', plain,
% 1.00/1.20      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.00/1.20        | (v2_funct_1 @ sk_C)
% 1.00/1.20        | ((sk_A) = (k1_xboole_0))
% 1.00/1.20        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.00/1.20        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.00/1.20        | ~ (v1_funct_1 @ sk_C))),
% 1.00/1.20      inference('sup-', [status(thm)], ['63', '69'])).
% 1.00/1.20  thf('71', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 1.00/1.20      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.00/1.20  thf('72', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('73', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('75', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.20      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 1.00/1.20  thf('76', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.00/1.20      inference('split', [status(esa)], ['8'])).
% 1.00/1.20  thf('77', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.00/1.20      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 1.00/1.20  thf('78', plain, (~ (v2_funct_1 @ sk_C)),
% 1.00/1.20      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 1.00/1.20  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.20      inference('clc', [status(thm)], ['75', '78'])).
% 1.00/1.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.00/1.20  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.20  thf('81', plain, ((v1_xboole_0 @ sk_C)),
% 1.00/1.20      inference('demod', [status(thm)], ['48', '79', '80'])).
% 1.00/1.20  thf('82', plain, ($false), inference('demod', [status(thm)], ['45', '81'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.06/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
