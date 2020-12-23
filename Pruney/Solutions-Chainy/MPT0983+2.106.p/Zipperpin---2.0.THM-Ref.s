%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ga6RhF4CmM

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:18 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 357 expanded)
%              Number of leaves         :   42 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          : 1256 (7329 expanded)
%              Number of equality atoms :   43 (  81 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
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
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('11',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_partfun1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ X38 )
       != X37 )
      | ( v2_funct_2 @ X38 @ X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,(
    ! [X38: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v5_relat_1 @ X38 @ ( k2_relat_1 @ X38 ) )
      | ( v2_funct_2 @ X38 @ ( k2_relat_1 @ X38 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['32','35','36','41'])).

thf('43',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['14','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50 ) )
      | ( v2_funct_1 @ X54 )
      | ( X52 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X51 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('72',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('73',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['70','73'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('80',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('85',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','87'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('89',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','90'])).

thf('92',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('93',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','93','94'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['50','95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['47','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ga6RhF4CmM
% 0.16/0.37  % Computer   : n014.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:01:52 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.82/2.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.82/2.02  % Solved by: fo/fo7.sh
% 1.82/2.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.02  % done 1694 iterations in 1.531s
% 1.82/2.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.82/2.02  % SZS output start Refutation
% 1.82/2.02  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.82/2.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.82/2.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.82/2.02  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.82/2.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.82/2.02  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.82/2.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.82/2.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.82/2.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.82/2.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.82/2.02  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.82/2.02  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.82/2.02  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.82/2.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.82/2.02  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.82/2.02  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.82/2.02  thf(sk_C_type, type, sk_C: $i).
% 1.82/2.02  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.82/2.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.82/2.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.82/2.02  thf(sk_D_type, type, sk_D: $i).
% 1.82/2.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.82/2.02  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.82/2.02  thf(t29_relset_1, axiom,
% 1.82/2.02    (![A:$i]:
% 1.82/2.02     ( m1_subset_1 @
% 1.82/2.02       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.82/2.02  thf('0', plain,
% 1.82/2.02      (![X36 : $i]:
% 1.82/2.02         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 1.82/2.02          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.82/2.02      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.82/2.02  thf(redefinition_k6_partfun1, axiom,
% 1.82/2.02    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.82/2.02  thf('1', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.82/2.02      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.82/2.02  thf('2', plain,
% 1.82/2.02      (![X36 : $i]:
% 1.82/2.02         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 1.82/2.02          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.82/2.02      inference('demod', [status(thm)], ['0', '1'])).
% 1.82/2.02  thf(cc3_relset_1, axiom,
% 1.82/2.02    (![A:$i,B:$i]:
% 1.82/2.02     ( ( v1_xboole_0 @ A ) =>
% 1.82/2.02       ( ![C:$i]:
% 1.82/2.02         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.02           ( v1_xboole_0 @ C ) ) ) ))).
% 1.82/2.02  thf('3', plain,
% 1.82/2.02      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.82/2.02         (~ (v1_xboole_0 @ X14)
% 1.82/2.02          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 1.82/2.02          | (v1_xboole_0 @ X15))),
% 1.82/2.02      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.82/2.02  thf('4', plain,
% 1.82/2.02      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.82/2.02      inference('sup-', [status(thm)], ['2', '3'])).
% 1.82/2.02  thf(t8_boole, axiom,
% 1.82/2.02    (![A:$i,B:$i]:
% 1.82/2.02     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.82/2.02  thf('5', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i]:
% 1.82/2.02         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [t8_boole])).
% 1.82/2.02  thf('6', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i]:
% 1.82/2.02         (~ (v1_xboole_0 @ X0)
% 1.82/2.02          | ((k6_partfun1 @ X0) = (X1))
% 1.82/2.02          | ~ (v1_xboole_0 @ X1))),
% 1.82/2.02      inference('sup-', [status(thm)], ['4', '5'])).
% 1.82/2.02  thf(t29_funct_2, conjecture,
% 1.82/2.02    (![A:$i,B:$i,C:$i]:
% 1.82/2.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.02       ( ![D:$i]:
% 1.82/2.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.82/2.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.82/2.02           ( ( r2_relset_1 @
% 1.82/2.02               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.82/2.02               ( k6_partfun1 @ A ) ) =>
% 1.82/2.02             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.82/2.02  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.02    (~( ![A:$i,B:$i,C:$i]:
% 1.82/2.02        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.02            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.02          ( ![D:$i]:
% 1.82/2.02            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.82/2.02                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.82/2.02              ( ( r2_relset_1 @
% 1.82/2.02                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.82/2.02                  ( k6_partfun1 @ A ) ) =>
% 1.82/2.02                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.82/2.02    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.82/2.02  thf('7', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('8', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.82/2.02      inference('split', [status(esa)], ['7'])).
% 1.82/2.02  thf('9', plain,
% 1.82/2.02      ((![X0 : $i]:
% 1.82/2.02          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.82/2.02           | ~ (v1_xboole_0 @ sk_C)
% 1.82/2.02           | ~ (v1_xboole_0 @ X0)))
% 1.82/2.02         <= (~ ((v2_funct_1 @ sk_C)))),
% 1.82/2.02      inference('sup-', [status(thm)], ['6', '8'])).
% 1.82/2.02  thf(fc4_funct_1, axiom,
% 1.82/2.02    (![A:$i]:
% 1.82/2.02     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.82/2.02       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.82/2.02  thf('10', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 1.82/2.02      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.82/2.02  thf('11', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.82/2.02      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.82/2.02  thf('12', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 1.82/2.02      inference('demod', [status(thm)], ['10', '11'])).
% 1.82/2.02  thf('13', plain,
% 1.82/2.02      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 1.82/2.02         <= (~ ((v2_funct_1 @ sk_C)))),
% 1.82/2.02      inference('demod', [status(thm)], ['9', '12'])).
% 1.82/2.02  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.82/2.02      inference('condensation', [status(thm)], ['13'])).
% 1.82/2.02  thf('15', plain,
% 1.82/2.02      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.82/2.02        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.82/2.02        (k6_partfun1 @ sk_A))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('16', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(t24_funct_2, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i]:
% 1.82/2.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.02       ( ![D:$i]:
% 1.82/2.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.82/2.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.82/2.02           ( ( r2_relset_1 @
% 1.82/2.02               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.82/2.02               ( k6_partfun1 @ B ) ) =>
% 1.82/2.02             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.82/2.02  thf('17', plain,
% 1.82/2.02      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.82/2.02         (~ (v1_funct_1 @ X46)
% 1.82/2.02          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 1.82/2.02          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.82/2.02          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 1.82/2.02               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 1.82/2.02               (k6_partfun1 @ X47))
% 1.82/2.02          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 1.82/2.02          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 1.82/2.02          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 1.82/2.02          | ~ (v1_funct_1 @ X49))),
% 1.82/2.02      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.82/2.02  thf('18', plain,
% 1.82/2.02      (![X0 : $i]:
% 1.82/2.02         (~ (v1_funct_1 @ X0)
% 1.82/2.02          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.82/2.02          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 1.82/2.02          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.82/2.02               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 1.82/2.02               (k6_partfun1 @ sk_A))
% 1.82/2.02          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 1.82/2.02          | ~ (v1_funct_1 @ sk_C))),
% 1.82/2.02      inference('sup-', [status(thm)], ['16', '17'])).
% 1.82/2.02  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('21', plain,
% 1.82/2.02      (![X0 : $i]:
% 1.82/2.02         (~ (v1_funct_1 @ X0)
% 1.82/2.02          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.82/2.02          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 1.82/2.02          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.82/2.02               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 1.82/2.02               (k6_partfun1 @ sk_A)))),
% 1.82/2.02      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.82/2.02  thf('22', plain,
% 1.82/2.02      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 1.82/2.02        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 1.82/2.02        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 1.82/2.02        | ~ (v1_funct_1 @ sk_D))),
% 1.82/2.02      inference('sup-', [status(thm)], ['15', '21'])).
% 1.82/2.02  thf('23', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(redefinition_k2_relset_1, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i]:
% 1.82/2.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.02       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.82/2.02  thf('24', plain,
% 1.82/2.02      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.82/2.02         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.82/2.02          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.82/2.02      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.82/2.02  thf('25', plain,
% 1.82/2.02      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.82/2.02      inference('sup-', [status(thm)], ['23', '24'])).
% 1.82/2.02  thf('26', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.82/2.02      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.82/2.02  thf(d3_funct_2, axiom,
% 1.82/2.02    (![A:$i,B:$i]:
% 1.82/2.02     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.82/2.02       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.82/2.02  thf('30', plain,
% 1.82/2.02      (![X37 : $i, X38 : $i]:
% 1.82/2.02         (((k2_relat_1 @ X38) != (X37))
% 1.82/2.02          | (v2_funct_2 @ X38 @ X37)
% 1.82/2.02          | ~ (v5_relat_1 @ X38 @ X37)
% 1.82/2.02          | ~ (v1_relat_1 @ X38))),
% 1.82/2.02      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.82/2.02  thf('31', plain,
% 1.82/2.02      (![X38 : $i]:
% 1.82/2.02         (~ (v1_relat_1 @ X38)
% 1.82/2.02          | ~ (v5_relat_1 @ X38 @ (k2_relat_1 @ X38))
% 1.82/2.02          | (v2_funct_2 @ X38 @ (k2_relat_1 @ X38)))),
% 1.82/2.02      inference('simplify', [status(thm)], ['30'])).
% 1.82/2.02  thf('32', plain,
% 1.82/2.02      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.82/2.02        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.82/2.02        | ~ (v1_relat_1 @ sk_D))),
% 1.82/2.02      inference('sup-', [status(thm)], ['29', '31'])).
% 1.82/2.02  thf('33', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(cc2_relset_1, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i]:
% 1.82/2.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.02       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.82/2.02  thf('34', plain,
% 1.82/2.02      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.82/2.02         ((v5_relat_1 @ X11 @ X13)
% 1.82/2.02          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.82/2.02      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.82/2.02  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.82/2.02      inference('sup-', [status(thm)], ['33', '34'])).
% 1.82/2.02  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.82/2.02      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.82/2.02  thf('37', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(cc2_relat_1, axiom,
% 1.82/2.02    (![A:$i]:
% 1.82/2.02     ( ( v1_relat_1 @ A ) =>
% 1.82/2.02       ( ![B:$i]:
% 1.82/2.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.82/2.02  thf('38', plain,
% 1.82/2.02      (![X5 : $i, X6 : $i]:
% 1.82/2.02         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.82/2.02          | (v1_relat_1 @ X5)
% 1.82/2.02          | ~ (v1_relat_1 @ X6))),
% 1.82/2.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.82/2.02  thf('39', plain,
% 1.82/2.02      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.82/2.02      inference('sup-', [status(thm)], ['37', '38'])).
% 1.82/2.02  thf(fc6_relat_1, axiom,
% 1.82/2.02    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.82/2.02  thf('40', plain,
% 1.82/2.02      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.82/2.02      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.82/2.02  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.82/2.02      inference('demod', [status(thm)], ['39', '40'])).
% 1.82/2.02  thf('42', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.82/2.02      inference('demod', [status(thm)], ['32', '35', '36', '41'])).
% 1.82/2.02  thf('43', plain,
% 1.82/2.02      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.82/2.02      inference('split', [status(esa)], ['7'])).
% 1.82/2.02  thf('44', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.82/2.02      inference('sup-', [status(thm)], ['42', '43'])).
% 1.82/2.02  thf('45', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.82/2.02      inference('split', [status(esa)], ['7'])).
% 1.82/2.02  thf('46', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.82/2.02      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 1.82/2.02  thf('47', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.82/2.02      inference('simpl_trail', [status(thm)], ['14', '46'])).
% 1.82/2.02  thf('48', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('49', plain,
% 1.82/2.02      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.82/2.02         (~ (v1_xboole_0 @ X14)
% 1.82/2.02          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 1.82/2.02          | (v1_xboole_0 @ X15))),
% 1.82/2.02      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.82/2.02  thf('50', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.82/2.02      inference('sup-', [status(thm)], ['48', '49'])).
% 1.82/2.02  thf('51', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('52', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(redefinition_k1_partfun1, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.82/2.02     ( ( ( v1_funct_1 @ E ) & 
% 1.82/2.02         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.82/2.02         ( v1_funct_1 @ F ) & 
% 1.82/2.02         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.82/2.02       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.82/2.02  thf('53', plain,
% 1.82/2.02      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.82/2.02         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.82/2.02          | ~ (v1_funct_1 @ X39)
% 1.82/2.02          | ~ (v1_funct_1 @ X42)
% 1.82/2.02          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.82/2.02          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 1.82/2.02              = (k5_relat_1 @ X39 @ X42)))),
% 1.82/2.02      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.82/2.02  thf('54', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.02         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 1.82/2.02            = (k5_relat_1 @ sk_C @ X0))
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.82/2.02          | ~ (v1_funct_1 @ X0)
% 1.82/2.02          | ~ (v1_funct_1 @ sk_C))),
% 1.82/2.02      inference('sup-', [status(thm)], ['52', '53'])).
% 1.82/2.02  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('56', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.02         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 1.82/2.02            = (k5_relat_1 @ sk_C @ X0))
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.82/2.02          | ~ (v1_funct_1 @ X0))),
% 1.82/2.02      inference('demod', [status(thm)], ['54', '55'])).
% 1.82/2.02  thf('57', plain,
% 1.82/2.02      ((~ (v1_funct_1 @ sk_D)
% 1.82/2.02        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 1.82/2.02            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.82/2.02      inference('sup-', [status(thm)], ['51', '56'])).
% 1.82/2.02  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('59', plain,
% 1.82/2.02      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 1.82/2.02         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.82/2.02      inference('demod', [status(thm)], ['57', '58'])).
% 1.82/2.02  thf('60', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(t26_funct_2, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i,D:$i]:
% 1.82/2.02     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.82/2.02         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.02       ( ![E:$i]:
% 1.82/2.02         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.82/2.02             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.82/2.02           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.82/2.02             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.82/2.02               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.82/2.02  thf('61', plain,
% 1.82/2.02      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.82/2.02         (~ (v1_funct_1 @ X50)
% 1.82/2.02          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 1.82/2.02          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 1.82/2.02          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50))
% 1.82/2.02          | (v2_funct_1 @ X54)
% 1.82/2.02          | ((X52) = (k1_xboole_0))
% 1.82/2.02          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.82/2.02          | ~ (v1_funct_2 @ X54 @ X53 @ X51)
% 1.82/2.02          | ~ (v1_funct_1 @ X54))),
% 1.82/2.02      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.82/2.02  thf('62', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i]:
% 1.82/2.02         (~ (v1_funct_1 @ X0)
% 1.82/2.02          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.82/2.02          | ((sk_A) = (k1_xboole_0))
% 1.82/2.02          | (v2_funct_1 @ X0)
% 1.82/2.02          | ~ (v2_funct_1 @ 
% 1.82/2.02               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 1.82/2.02          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 1.82/2.02          | ~ (v1_funct_1 @ sk_D))),
% 1.82/2.02      inference('sup-', [status(thm)], ['60', '61'])).
% 1.82/2.02  thf('63', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('65', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i]:
% 1.82/2.02         (~ (v1_funct_1 @ X0)
% 1.82/2.02          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.82/2.02          | ((sk_A) = (k1_xboole_0))
% 1.82/2.02          | (v2_funct_1 @ X0)
% 1.82/2.02          | ~ (v2_funct_1 @ 
% 1.82/2.02               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 1.82/2.02      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.82/2.02  thf('66', plain,
% 1.82/2.02      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.82/2.02        | (v2_funct_1 @ sk_C)
% 1.82/2.02        | ((sk_A) = (k1_xboole_0))
% 1.82/2.02        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.82/2.02        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 1.82/2.02        | ~ (v1_funct_1 @ sk_C))),
% 1.82/2.02      inference('sup-', [status(thm)], ['59', '65'])).
% 1.82/2.02  thf('67', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('70', plain,
% 1.82/2.02      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.82/2.02        | (v2_funct_1 @ sk_C)
% 1.82/2.02        | ((sk_A) = (k1_xboole_0)))),
% 1.82/2.02      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 1.82/2.02  thf('71', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.82/2.02      inference('split', [status(esa)], ['7'])).
% 1.82/2.02  thf('72', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.82/2.02      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 1.82/2.02  thf('73', plain, (~ (v2_funct_1 @ sk_C)),
% 1.82/2.02      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 1.82/2.02  thf('74', plain,
% 1.82/2.02      ((((sk_A) = (k1_xboole_0)) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 1.82/2.02      inference('clc', [status(thm)], ['70', '73'])).
% 1.82/2.02  thf('75', plain,
% 1.82/2.02      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.82/2.02        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.82/2.02        (k6_partfun1 @ sk_A))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('76', plain,
% 1.82/2.02      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 1.82/2.02         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.82/2.02      inference('demod', [status(thm)], ['57', '58'])).
% 1.82/2.02  thf('77', plain,
% 1.82/2.02      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.82/2.02        (k6_partfun1 @ sk_A))),
% 1.82/2.02      inference('demod', [status(thm)], ['75', '76'])).
% 1.82/2.02  thf('78', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('79', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(dt_k4_relset_1, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.82/2.02     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.82/2.02         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.82/2.02       ( m1_subset_1 @
% 1.82/2.02         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.82/2.02         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.82/2.02  thf('80', plain,
% 1.82/2.02      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.82/2.02         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.82/2.02          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.82/2.02          | (m1_subset_1 @ (k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 1.82/2.02             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 1.82/2.02      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.82/2.02  thf('81', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.02         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 1.82/2.02           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.82/2.02          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.82/2.02      inference('sup-', [status(thm)], ['79', '80'])).
% 1.82/2.02  thf('82', plain,
% 1.82/2.02      ((m1_subset_1 @ 
% 1.82/2.02        (k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.82/2.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.82/2.02      inference('sup-', [status(thm)], ['78', '81'])).
% 1.82/2.02  thf('83', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf('84', plain,
% 1.82/2.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.82/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.02  thf(redefinition_k4_relset_1, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.82/2.02     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.82/2.02         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.82/2.02       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.82/2.02  thf('85', plain,
% 1.82/2.02      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.82/2.02         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.82/2.02          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.82/2.02          | ((k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.82/2.02              = (k5_relat_1 @ X26 @ X29)))),
% 1.82/2.02      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.82/2.02  thf('86', plain,
% 1.82/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.02         (((k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 1.82/2.02            = (k5_relat_1 @ sk_C @ X0))
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.82/2.02      inference('sup-', [status(thm)], ['84', '85'])).
% 1.82/2.02  thf('87', plain,
% 1.82/2.02      (((k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 1.82/2.02         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.82/2.02      inference('sup-', [status(thm)], ['83', '86'])).
% 1.82/2.02  thf('88', plain,
% 1.82/2.02      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.82/2.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.82/2.02      inference('demod', [status(thm)], ['82', '87'])).
% 1.82/2.02  thf(redefinition_r2_relset_1, axiom,
% 1.82/2.02    (![A:$i,B:$i,C:$i,D:$i]:
% 1.82/2.02     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.82/2.02         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.02       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.82/2.02  thf('89', plain,
% 1.82/2.02      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.82/2.02         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.82/2.02          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.82/2.02          | ((X32) = (X35))
% 1.82/2.02          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 1.82/2.02      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.82/2.02  thf('90', plain,
% 1.82/2.02      (![X0 : $i]:
% 1.82/2.02         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.82/2.02          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.82/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.82/2.02      inference('sup-', [status(thm)], ['88', '89'])).
% 1.82/2.02  thf('91', plain,
% 1.82/2.02      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.82/2.02           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.82/2.02        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.82/2.02      inference('sup-', [status(thm)], ['77', '90'])).
% 1.82/2.02  thf('92', plain,
% 1.82/2.02      (![X36 : $i]:
% 1.82/2.02         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 1.82/2.02          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.82/2.02      inference('demod', [status(thm)], ['0', '1'])).
% 1.82/2.02  thf('93', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.82/2.02      inference('demod', [status(thm)], ['91', '92'])).
% 1.82/2.02  thf('94', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 1.82/2.02      inference('demod', [status(thm)], ['10', '11'])).
% 1.82/2.02  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 1.82/2.02      inference('demod', [status(thm)], ['74', '93', '94'])).
% 1.82/2.02  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.82/2.02  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.82/2.02      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.82/2.02  thf('97', plain, ((v1_xboole_0 @ sk_C)),
% 1.82/2.02      inference('demod', [status(thm)], ['50', '95', '96'])).
% 1.82/2.02  thf('98', plain, ($false), inference('demod', [status(thm)], ['47', '97'])).
% 1.82/2.02  
% 1.82/2.02  % SZS output end Refutation
% 1.82/2.02  
% 1.82/2.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
