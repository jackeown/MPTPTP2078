%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xrnKLHcoFe

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:04 EST 2020

% Result     : Theorem 5.10s
% Output     : Refutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 351 expanded)
%              Number of leaves         :   41 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          : 1240 (7299 expanded)
%              Number of equality atoms :   43 (  81 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('11',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('17',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_partfun1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k2_relat_1 @ X37 )
       != X36 )
      | ( v2_funct_2 @ X37 @ X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,(
    ! [X37: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v5_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
      | ( v2_funct_2 @ X37 @ ( k2_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    inference(split,[status(esa)],['7'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['14','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('51',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('59',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49 ) )
      | ( v2_funct_1 @ X53 )
      | ( X51 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X50 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('71',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('79',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('87',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('89',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','87','88'])).

thf('90',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('91',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('92',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['89','92'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['48','93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['45','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xrnKLHcoFe
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.10/5.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.10/5.33  % Solved by: fo/fo7.sh
% 5.10/5.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.10/5.33  % done 4186 iterations in 4.866s
% 5.10/5.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.10/5.33  % SZS output start Refutation
% 5.10/5.33  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.10/5.33  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.10/5.33  thf(sk_D_type, type, sk_D: $i).
% 5.10/5.33  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.10/5.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.10/5.33  thf(sk_C_type, type, sk_C: $i).
% 5.10/5.33  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.10/5.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.10/5.33  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.10/5.33  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.10/5.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.10/5.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.10/5.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.10/5.33  thf(sk_A_type, type, sk_A: $i).
% 5.10/5.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.10/5.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.10/5.33  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.10/5.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.10/5.33  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.10/5.33  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 5.10/5.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.10/5.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.10/5.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.10/5.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.10/5.33  thf(t29_relset_1, axiom,
% 5.10/5.33    (![A:$i]:
% 5.10/5.33     ( m1_subset_1 @
% 5.10/5.33       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.10/5.33  thf('0', plain,
% 5.10/5.33      (![X35 : $i]:
% 5.10/5.33         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 5.10/5.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.10/5.33      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.10/5.33  thf(redefinition_k6_partfun1, axiom,
% 5.10/5.33    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.10/5.33  thf('1', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.10/5.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.10/5.33  thf('2', plain,
% 5.10/5.33      (![X35 : $i]:
% 5.10/5.33         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 5.10/5.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.10/5.33      inference('demod', [status(thm)], ['0', '1'])).
% 5.10/5.33  thf(cc3_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i]:
% 5.10/5.33     ( ( v1_xboole_0 @ A ) =>
% 5.10/5.33       ( ![C:$i]:
% 5.10/5.33         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.10/5.33           ( v1_xboole_0 @ C ) ) ) ))).
% 5.10/5.33  thf('3', plain,
% 5.10/5.33      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.10/5.33         (~ (v1_xboole_0 @ X13)
% 5.10/5.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X15)))
% 5.10/5.33          | (v1_xboole_0 @ X14))),
% 5.10/5.33      inference('cnf', [status(esa)], [cc3_relset_1])).
% 5.10/5.33  thf('4', plain,
% 5.10/5.33      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.10/5.33      inference('sup-', [status(thm)], ['2', '3'])).
% 5.10/5.33  thf(t8_boole, axiom,
% 5.10/5.33    (![A:$i,B:$i]:
% 5.10/5.33     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 5.10/5.33  thf('5', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i]:
% 5.10/5.33         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [t8_boole])).
% 5.10/5.33  thf('6', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i]:
% 5.10/5.33         (~ (v1_xboole_0 @ X0)
% 5.10/5.33          | ((k6_partfun1 @ X0) = (X1))
% 5.10/5.33          | ~ (v1_xboole_0 @ X1))),
% 5.10/5.33      inference('sup-', [status(thm)], ['4', '5'])).
% 5.10/5.33  thf(t29_funct_2, conjecture,
% 5.10/5.33    (![A:$i,B:$i,C:$i]:
% 5.10/5.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.10/5.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.10/5.33       ( ![D:$i]:
% 5.10/5.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.10/5.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.10/5.33           ( ( r2_relset_1 @
% 5.10/5.33               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.10/5.33               ( k6_partfun1 @ A ) ) =>
% 5.10/5.33             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 5.10/5.33  thf(zf_stmt_0, negated_conjecture,
% 5.10/5.33    (~( ![A:$i,B:$i,C:$i]:
% 5.10/5.33        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.10/5.33            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.10/5.33          ( ![D:$i]:
% 5.10/5.33            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.10/5.33                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.10/5.33              ( ( r2_relset_1 @
% 5.10/5.33                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.10/5.33                  ( k6_partfun1 @ A ) ) =>
% 5.10/5.33                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 5.10/5.33    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 5.10/5.33  thf('7', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('8', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.10/5.33      inference('split', [status(esa)], ['7'])).
% 5.10/5.33  thf('9', plain,
% 5.10/5.33      ((![X0 : $i]:
% 5.10/5.33          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 5.10/5.33           | ~ (v1_xboole_0 @ sk_C)
% 5.10/5.33           | ~ (v1_xboole_0 @ X0)))
% 5.10/5.33         <= (~ ((v2_funct_1 @ sk_C)))),
% 5.10/5.33      inference('sup-', [status(thm)], ['6', '8'])).
% 5.10/5.33  thf(fc4_funct_1, axiom,
% 5.10/5.33    (![A:$i]:
% 5.10/5.33     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.10/5.33       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.10/5.33  thf('10', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 5.10/5.33      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.10/5.33  thf('11', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.10/5.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.10/5.33  thf('12', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 5.10/5.33      inference('demod', [status(thm)], ['10', '11'])).
% 5.10/5.33  thf('13', plain,
% 5.10/5.33      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 5.10/5.33         <= (~ ((v2_funct_1 @ sk_C)))),
% 5.10/5.33      inference('demod', [status(thm)], ['9', '12'])).
% 5.10/5.33  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.10/5.33      inference('condensation', [status(thm)], ['13'])).
% 5.10/5.33  thf('15', plain,
% 5.10/5.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.10/5.33        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.10/5.33        (k6_partfun1 @ sk_A))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('16', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(t24_funct_2, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i]:
% 5.10/5.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.10/5.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.10/5.33       ( ![D:$i]:
% 5.10/5.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.10/5.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.10/5.33           ( ( r2_relset_1 @
% 5.10/5.33               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 5.10/5.33               ( k6_partfun1 @ B ) ) =>
% 5.10/5.33             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 5.10/5.33  thf('17', plain,
% 5.10/5.33      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.10/5.33         (~ (v1_funct_1 @ X45)
% 5.10/5.33          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 5.10/5.33          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 5.10/5.33          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 5.10/5.33               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 5.10/5.33               (k6_partfun1 @ X46))
% 5.10/5.33          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 5.10/5.33          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 5.10/5.33          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 5.10/5.33          | ~ (v1_funct_1 @ X48))),
% 5.10/5.33      inference('cnf', [status(esa)], [t24_funct_2])).
% 5.10/5.33  thf('18', plain,
% 5.10/5.33      (![X0 : $i]:
% 5.10/5.33         (~ (v1_funct_1 @ X0)
% 5.10/5.33          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 5.10/5.33          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 5.10/5.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.10/5.33               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 5.10/5.33               (k6_partfun1 @ sk_A))
% 5.10/5.33          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 5.10/5.33          | ~ (v1_funct_1 @ sk_C))),
% 5.10/5.33      inference('sup-', [status(thm)], ['16', '17'])).
% 5.10/5.33  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('21', plain,
% 5.10/5.33      (![X0 : $i]:
% 5.10/5.33         (~ (v1_funct_1 @ X0)
% 5.10/5.33          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 5.10/5.33          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 5.10/5.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.10/5.33               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 5.10/5.33               (k6_partfun1 @ sk_A)))),
% 5.10/5.33      inference('demod', [status(thm)], ['18', '19', '20'])).
% 5.10/5.33  thf('22', plain,
% 5.10/5.33      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 5.10/5.33        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 5.10/5.33        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 5.10/5.33        | ~ (v1_funct_1 @ sk_D))),
% 5.10/5.33      inference('sup-', [status(thm)], ['15', '21'])).
% 5.10/5.33  thf('23', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(redefinition_k2_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i]:
% 5.10/5.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.10/5.33       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.10/5.33  thf('24', plain,
% 5.10/5.33      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.10/5.33         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 5.10/5.33          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.10/5.33      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.10/5.33  thf('25', plain,
% 5.10/5.33      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.10/5.33      inference('sup-', [status(thm)], ['23', '24'])).
% 5.10/5.33  thf('26', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.10/5.33      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 5.10/5.33  thf(d3_funct_2, axiom,
% 5.10/5.33    (![A:$i,B:$i]:
% 5.10/5.33     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.10/5.33       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.10/5.33  thf('30', plain,
% 5.10/5.33      (![X36 : $i, X37 : $i]:
% 5.10/5.33         (((k2_relat_1 @ X37) != (X36))
% 5.10/5.33          | (v2_funct_2 @ X37 @ X36)
% 5.10/5.33          | ~ (v5_relat_1 @ X37 @ X36)
% 5.10/5.33          | ~ (v1_relat_1 @ X37))),
% 5.10/5.33      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.10/5.33  thf('31', plain,
% 5.10/5.33      (![X37 : $i]:
% 5.10/5.33         (~ (v1_relat_1 @ X37)
% 5.10/5.33          | ~ (v5_relat_1 @ X37 @ (k2_relat_1 @ X37))
% 5.10/5.33          | (v2_funct_2 @ X37 @ (k2_relat_1 @ X37)))),
% 5.10/5.33      inference('simplify', [status(thm)], ['30'])).
% 5.10/5.33  thf('32', plain,
% 5.10/5.33      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 5.10/5.33        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 5.10/5.33        | ~ (v1_relat_1 @ sk_D))),
% 5.10/5.33      inference('sup-', [status(thm)], ['29', '31'])).
% 5.10/5.33  thf('33', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(cc2_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i]:
% 5.10/5.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.10/5.33       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.10/5.33  thf('34', plain,
% 5.10/5.33      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.10/5.33         ((v5_relat_1 @ X10 @ X12)
% 5.10/5.33          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 5.10/5.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.10/5.33  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 5.10/5.33      inference('sup-', [status(thm)], ['33', '34'])).
% 5.10/5.33  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.10/5.33      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 5.10/5.33  thf('37', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(cc1_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i]:
% 5.10/5.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.10/5.33       ( v1_relat_1 @ C ) ))).
% 5.10/5.33  thf('38', plain,
% 5.10/5.33      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.10/5.33         ((v1_relat_1 @ X7)
% 5.10/5.33          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 5.10/5.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.10/5.33  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 5.10/5.33      inference('sup-', [status(thm)], ['37', '38'])).
% 5.10/5.33  thf('40', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 5.10/5.33      inference('demod', [status(thm)], ['32', '35', '36', '39'])).
% 5.10/5.33  thf('41', plain,
% 5.10/5.33      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.10/5.33      inference('split', [status(esa)], ['7'])).
% 5.10/5.33  thf('42', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 5.10/5.33      inference('sup-', [status(thm)], ['40', '41'])).
% 5.10/5.33  thf('43', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 5.10/5.33      inference('split', [status(esa)], ['7'])).
% 5.10/5.33  thf('44', plain, (~ ((v2_funct_1 @ sk_C))),
% 5.10/5.33      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 5.10/5.33  thf('45', plain, (~ (v1_xboole_0 @ sk_C)),
% 5.10/5.33      inference('simpl_trail', [status(thm)], ['14', '44'])).
% 5.10/5.33  thf('46', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('47', plain,
% 5.10/5.33      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.10/5.33         (~ (v1_xboole_0 @ X13)
% 5.10/5.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X15)))
% 5.10/5.33          | (v1_xboole_0 @ X14))),
% 5.10/5.33      inference('cnf', [status(esa)], [cc3_relset_1])).
% 5.10/5.33  thf('48', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 5.10/5.33      inference('sup-', [status(thm)], ['46', '47'])).
% 5.10/5.33  thf('49', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('50', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(redefinition_k1_partfun1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.10/5.33     ( ( ( v1_funct_1 @ E ) & 
% 5.10/5.33         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.10/5.33         ( v1_funct_1 @ F ) & 
% 5.10/5.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.10/5.33       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.10/5.33  thf('51', plain,
% 5.10/5.33      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.10/5.33         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.10/5.33          | ~ (v1_funct_1 @ X38)
% 5.10/5.33          | ~ (v1_funct_1 @ X41)
% 5.10/5.33          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.10/5.33          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 5.10/5.33              = (k5_relat_1 @ X38 @ X41)))),
% 5.10/5.33      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.10/5.33  thf('52', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.10/5.33         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 5.10/5.33            = (k5_relat_1 @ sk_C @ X0))
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.10/5.33          | ~ (v1_funct_1 @ X0)
% 5.10/5.33          | ~ (v1_funct_1 @ sk_C))),
% 5.10/5.33      inference('sup-', [status(thm)], ['50', '51'])).
% 5.10/5.33  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('54', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.10/5.33         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 5.10/5.33            = (k5_relat_1 @ sk_C @ X0))
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.10/5.33          | ~ (v1_funct_1 @ X0))),
% 5.10/5.33      inference('demod', [status(thm)], ['52', '53'])).
% 5.10/5.33  thf('55', plain,
% 5.10/5.33      ((~ (v1_funct_1 @ sk_D)
% 5.10/5.33        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 5.10/5.33            = (k5_relat_1 @ sk_C @ sk_D)))),
% 5.10/5.33      inference('sup-', [status(thm)], ['49', '54'])).
% 5.10/5.33  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('57', plain,
% 5.10/5.33      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 5.10/5.33         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.10/5.33      inference('demod', [status(thm)], ['55', '56'])).
% 5.10/5.33  thf('58', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(t26_funct_2, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i,D:$i]:
% 5.10/5.33     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.10/5.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.10/5.33       ( ![E:$i]:
% 5.10/5.33         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.10/5.33             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.10/5.33           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 5.10/5.33             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 5.10/5.33               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 5.10/5.33  thf('59', plain,
% 5.10/5.33      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.10/5.33         (~ (v1_funct_1 @ X49)
% 5.10/5.33          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 5.10/5.33          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 5.10/5.33          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49))
% 5.10/5.33          | (v2_funct_1 @ X53)
% 5.10/5.33          | ((X51) = (k1_xboole_0))
% 5.10/5.33          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 5.10/5.33          | ~ (v1_funct_2 @ X53 @ X52 @ X50)
% 5.10/5.33          | ~ (v1_funct_1 @ X53))),
% 5.10/5.33      inference('cnf', [status(esa)], [t26_funct_2])).
% 5.10/5.33  thf('60', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i]:
% 5.10/5.33         (~ (v1_funct_1 @ X0)
% 5.10/5.33          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.10/5.33          | ((sk_A) = (k1_xboole_0))
% 5.10/5.33          | (v2_funct_1 @ X0)
% 5.10/5.33          | ~ (v2_funct_1 @ 
% 5.10/5.33               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 5.10/5.33          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 5.10/5.33          | ~ (v1_funct_1 @ sk_D))),
% 5.10/5.33      inference('sup-', [status(thm)], ['58', '59'])).
% 5.10/5.33  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('63', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i]:
% 5.10/5.33         (~ (v1_funct_1 @ X0)
% 5.10/5.33          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.10/5.33          | ((sk_A) = (k1_xboole_0))
% 5.10/5.33          | (v2_funct_1 @ X0)
% 5.10/5.33          | ~ (v2_funct_1 @ 
% 5.10/5.33               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 5.10/5.33      inference('demod', [status(thm)], ['60', '61', '62'])).
% 5.10/5.33  thf('64', plain,
% 5.10/5.33      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 5.10/5.33        | (v2_funct_1 @ sk_C)
% 5.10/5.33        | ((sk_A) = (k1_xboole_0))
% 5.10/5.33        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 5.10/5.33        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 5.10/5.33        | ~ (v1_funct_1 @ sk_C))),
% 5.10/5.33      inference('sup-', [status(thm)], ['57', '63'])).
% 5.10/5.33  thf('65', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('68', plain,
% 5.10/5.33      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 5.10/5.33        | (v2_funct_1 @ sk_C)
% 5.10/5.33        | ((sk_A) = (k1_xboole_0)))),
% 5.10/5.33      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 5.10/5.33  thf('69', plain,
% 5.10/5.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.10/5.33        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.10/5.33        (k6_partfun1 @ sk_A))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('70', plain,
% 5.10/5.33      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 5.10/5.33         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.10/5.33      inference('demod', [status(thm)], ['55', '56'])).
% 5.10/5.33  thf('71', plain,
% 5.10/5.33      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.10/5.33        (k6_partfun1 @ sk_A))),
% 5.10/5.33      inference('demod', [status(thm)], ['69', '70'])).
% 5.10/5.33  thf('72', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('73', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(dt_k4_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.10/5.33     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.10/5.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.10/5.33       ( m1_subset_1 @
% 5.10/5.33         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.10/5.33         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 5.10/5.33  thf('74', plain,
% 5.10/5.33      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 5.10/5.33         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 5.10/5.33          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 5.10/5.33          | (m1_subset_1 @ (k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 5.10/5.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 5.10/5.33      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 5.10/5.33  thf('75', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.10/5.33         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 5.10/5.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.10/5.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 5.10/5.33      inference('sup-', [status(thm)], ['73', '74'])).
% 5.10/5.33  thf('76', plain,
% 5.10/5.33      ((m1_subset_1 @ 
% 5.10/5.33        (k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.10/5.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.10/5.33      inference('sup-', [status(thm)], ['72', '75'])).
% 5.10/5.33  thf('77', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf('78', plain,
% 5.10/5.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.10/5.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.10/5.33  thf(redefinition_k4_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.10/5.33     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.10/5.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.10/5.33       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.10/5.33  thf('79', plain,
% 5.10/5.33      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 5.10/5.33         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.10/5.33          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.10/5.33          | ((k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 5.10/5.33              = (k5_relat_1 @ X25 @ X28)))),
% 5.10/5.33      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 5.10/5.33  thf('80', plain,
% 5.10/5.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.10/5.33         (((k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 5.10/5.33            = (k5_relat_1 @ sk_C @ X0))
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 5.10/5.33      inference('sup-', [status(thm)], ['78', '79'])).
% 5.10/5.33  thf('81', plain,
% 5.10/5.33      (((k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 5.10/5.33         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.10/5.33      inference('sup-', [status(thm)], ['77', '80'])).
% 5.10/5.33  thf('82', plain,
% 5.10/5.33      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.10/5.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.10/5.33      inference('demod', [status(thm)], ['76', '81'])).
% 5.10/5.33  thf(redefinition_r2_relset_1, axiom,
% 5.10/5.33    (![A:$i,B:$i,C:$i,D:$i]:
% 5.10/5.33     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.10/5.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.10/5.33       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.10/5.33  thf('83', plain,
% 5.10/5.33      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.10/5.33         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 5.10/5.33          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 5.10/5.33          | ((X31) = (X34))
% 5.10/5.33          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 5.10/5.33      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.10/5.33  thf('84', plain,
% 5.10/5.33      (![X0 : $i]:
% 5.10/5.33         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 5.10/5.33          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 5.10/5.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.10/5.33      inference('sup-', [status(thm)], ['82', '83'])).
% 5.10/5.33  thf('85', plain,
% 5.10/5.33      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.10/5.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.10/5.33        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 5.10/5.33      inference('sup-', [status(thm)], ['71', '84'])).
% 5.10/5.33  thf('86', plain,
% 5.10/5.33      (![X35 : $i]:
% 5.10/5.33         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 5.10/5.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.10/5.33      inference('demod', [status(thm)], ['0', '1'])).
% 5.10/5.33  thf('87', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 5.10/5.33      inference('demod', [status(thm)], ['85', '86'])).
% 5.10/5.33  thf('88', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 5.10/5.33      inference('demod', [status(thm)], ['10', '11'])).
% 5.10/5.33  thf('89', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.10/5.33      inference('demod', [status(thm)], ['68', '87', '88'])).
% 5.10/5.33  thf('90', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.10/5.33      inference('split', [status(esa)], ['7'])).
% 5.10/5.33  thf('91', plain, (~ ((v2_funct_1 @ sk_C))),
% 5.10/5.33      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 5.10/5.33  thf('92', plain, (~ (v2_funct_1 @ sk_C)),
% 5.10/5.33      inference('simpl_trail', [status(thm)], ['90', '91'])).
% 5.10/5.33  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 5.10/5.33      inference('clc', [status(thm)], ['89', '92'])).
% 5.10/5.33  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.10/5.33  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.10/5.33      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.10/5.33  thf('95', plain, ((v1_xboole_0 @ sk_C)),
% 5.10/5.33      inference('demod', [status(thm)], ['48', '93', '94'])).
% 5.10/5.33  thf('96', plain, ($false), inference('demod', [status(thm)], ['45', '95'])).
% 5.10/5.33  
% 5.10/5.33  % SZS output end Refutation
% 5.10/5.33  
% 5.10/5.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
