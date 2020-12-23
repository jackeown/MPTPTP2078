%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iauVpkqV0Z

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 136 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  707 (1262 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X15 ) @ ( u1_orders_2 @ X16 ) )
      | ( m1_yellow_0 @ X15 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_yellow_0 @ X0 @ X0 )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X0 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_yellow_0 @ X0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_yellow_0 @ X0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t17_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( m1_yellow_6 @ B @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_waybel_0 @ B @ A )
           => ( m1_yellow_6 @ B @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_yellow_6])).

thf('8',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('10',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t40_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X14 ) ) )
      | ( r2_relset_1 @ X11 @ X14 @ ( k2_partfun1 @ X11 @ X14 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ ( u1_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('17',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('22',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ ( u1_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19','24'])).

thf('26',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( X3 = X6 )
      | ~ ( r2_relset_1 @ X4 @ X5 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( u1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('36',plain,
    ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    = ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(d8_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( l1_waybel_0 @ C @ A )
             => ( ( m1_yellow_6 @ C @ A @ B )
              <=> ( ( m1_yellow_0 @ C @ B )
                  & ( ( u1_waybel_0 @ A @ C )
                    = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( m1_yellow_0 @ X23 @ X21 )
      | ( ( u1_waybel_0 @ X22 @ X23 )
       != ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) @ ( u1_waybel_0 @ X22 @ X21 ) @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_yellow_6 @ X23 @ X22 @ X21 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('38',plain,
    ( ( ( u1_waybel_0 @ sk_A @ sk_B )
     != ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( m1_yellow_6 @ sk_B @ sk_A @ sk_B )
    | ~ ( m1_yellow_0 @ sk_B @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( u1_waybel_0 @ sk_A @ sk_B )
     != ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ( m1_yellow_6 @ sk_B @ sk_A @ sk_B )
    | ~ ( m1_yellow_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ~ ( m1_yellow_0 @ sk_B @ sk_B )
    | ( m1_yellow_6 @ sk_B @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( m1_yellow_6 @ sk_B @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( m1_yellow_0 @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','45'])).

thf('47',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( l1_orders_2 @ X17 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('49',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['46','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iauVpkqV0Z
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 38 iterations in 0.037s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.54  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.54  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.54  thf(d13_yellow_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_orders_2 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_orders_2 @ B ) =>
% 0.21/0.54           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.21/0.54             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (l1_orders_2 @ X15)
% 0.21/0.54          | ~ (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (r1_tarski @ (u1_orders_2 @ X15) @ (u1_orders_2 @ X16))
% 0.21/0.54          | (m1_yellow_0 @ X15 @ X16)
% 0.21/0.54          | ~ (l1_orders_2 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_orders_2 @ X0)
% 0.21/0.54          | (m1_yellow_0 @ X0 @ X0)
% 0.21/0.54          | ~ (r1_tarski @ (u1_orders_2 @ X0) @ (u1_orders_2 @ X0))
% 0.21/0.54          | ~ (l1_orders_2 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_orders_2 @ X0) | (m1_yellow_0 @ X0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i]: ((m1_yellow_0 @ X0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.54  thf(t17_yellow_6, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( m1_yellow_6 @ B @ A @ B ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( l1_struct_0 @ A ) =>
% 0.21/0.54          ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( m1_yellow_6 @ B @ A @ B ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t17_yellow_6])).
% 0.21/0.54  thf('8', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_u1_waybel_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.21/0.54         ( v1_funct_2 @
% 0.21/0.54           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @
% 0.21/0.54           ( u1_waybel_0 @ A @ B ) @ 
% 0.21/0.54           ( k1_zfmisc_1 @
% 0.21/0.54             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (l1_struct_0 @ X19)
% 0.21/0.54          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.21/0.54          | (m1_subset_1 @ (u1_waybel_0 @ X19 @ X20) @ 
% 0.21/0.54             (k1_zfmisc_1 @ 
% 0.21/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19)))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ 
% 0.21/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(t40_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( r1_tarski @ A @ C ) =>
% 0.21/0.54         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X11 @ X12)
% 0.21/0.54          | ~ (v1_funct_1 @ X13)
% 0.21/0.54          | ~ (v1_funct_2 @ X13 @ X11 @ X14)
% 0.21/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X14)))
% 0.21/0.54          | (r2_relset_1 @ X11 @ X14 @ (k2_partfun1 @ X11 @ X14 @ X13 @ X12) @ 
% 0.21/0.54             X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t40_funct_2])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54            (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.54           (u1_waybel_0 @ sk_A @ sk_B))
% 0.21/0.54          | ~ (v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.54               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))
% 0.21/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (l1_struct_0 @ X19)
% 0.21/0.54          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.21/0.54          | (v1_funct_2 @ (u1_waybel_0 @ X19 @ X20) @ (u1_struct_0 @ X20) @ 
% 0.21/0.54             (u1_struct_0 @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54        (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (l1_struct_0 @ X19)
% 0.21/0.54          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.21/0.54          | (v1_funct_1 @ (u1_waybel_0 @ X19 @ X20)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54            (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.54           (u1_waybel_0 @ sk_A @ sk_B))
% 0.21/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '19', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54        (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54         (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.54        (u1_waybel_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(dt_k2_partfun1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.21/0.54         ( m1_subset_1 @
% 0.21/0.54           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.21/0.54           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.54          | ~ (v1_funct_1 @ X7)
% 0.21/0.54          | (m1_subset_1 @ (k2_partfun1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ 
% 0.21/0.54           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54            (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.54           (k1_zfmisc_1 @ 
% 0.21/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.54          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ 
% 0.21/0.54          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.54          (k1_zfmisc_1 @ 
% 0.21/0.54           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.54          | ((X3) = (X6))
% 0.21/0.54          | ~ (r2_relset_1 @ X4 @ X5 @ X3 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54              (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.54             X1)
% 0.21/0.54          | ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54              (u1_waybel_0 @ sk_A @ sk_B) @ X0) = (X1))
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ 
% 0.21/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.54        | ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54            (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.54            = (u1_waybel_0 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54         (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.54         = (u1_waybel_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf(d8_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( l1_waybel_0 @ C @ A ) =>
% 0.21/0.54               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.21/0.54                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.21/0.54                   ( ( u1_waybel_0 @ A @ C ) =
% 0.21/0.54                     ( k2_partfun1 @
% 0.21/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.54                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ X21 @ X22)
% 0.21/0.54          | ~ (m1_yellow_0 @ X23 @ X21)
% 0.21/0.54          | ((u1_waybel_0 @ X22 @ X23)
% 0.21/0.54              != (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22) @ 
% 0.21/0.54                  (u1_waybel_0 @ X22 @ X21) @ (u1_struct_0 @ X23)))
% 0.21/0.54          | (m1_yellow_6 @ X23 @ X22 @ X21)
% 0.21/0.54          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.21/0.54          | ~ (l1_struct_0 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((((u1_waybel_0 @ sk_A @ sk_B) != (u1_waybel_0 @ sk_A @ sk_B))
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.54        | (m1_yellow_6 @ sk_B @ sk_A @ sk_B)
% 0.21/0.54        | ~ (m1_yellow_0 @ sk_B @ sk_B)
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((((u1_waybel_0 @ sk_A @ sk_B) != (u1_waybel_0 @ sk_A @ sk_B))
% 0.21/0.54        | (m1_yellow_6 @ sk_B @ sk_A @ sk_B)
% 0.21/0.54        | ~ (m1_yellow_0 @ sk_B @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((~ (m1_yellow_0 @ sk_B @ sk_B) | (m1_yellow_6 @ sk_B @ sk_A @ sk_B))),
% 0.21/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.54  thf('44', plain, (~ (m1_yellow_6 @ sk_B @ sk_A @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain, (~ (m1_yellow_0 @ sk_B @ sk_B)),
% 0.21/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain, (~ (l1_orders_2 @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '45'])).
% 0.21/0.54  thf('47', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_waybel_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.54          | (l1_orders_2 @ X17)
% 0.21/0.54          | ~ (l1_struct_0 @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.54  thf('49', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain, ($false), inference('demod', [status(thm)], ['46', '51'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
