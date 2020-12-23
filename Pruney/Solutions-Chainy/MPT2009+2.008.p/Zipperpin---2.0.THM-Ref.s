%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n5PfFdBe1n

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 215 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   33
%              Number of atoms          : 1361 (2907 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('1',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(rc7_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ( v1_yellow_6 @ B @ A )
          & ( v7_waybel_0 @ B )
          & ( v6_waybel_0 @ B @ A )
          & ( v4_orders_2 @ B )
          & ~ ( v2_struct_0 @ B )
          & ( l1_waybel_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X21 ) @ X21 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc7_yellow_6])).

thf(dt_k4_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_6])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t8_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_9])).

thf('6',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('8',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( r1_waybel_0 @ X7 @ X6 @ X9 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( l1_orders_2 @ X15 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('19',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(d8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( ( k2_waybel_0 @ X13 @ X12 @ X14 )
        = ( k3_funct_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_waybel_0 @ X13 @ X12 ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_waybel_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B_1 ) @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B_1 ) @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('31',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t189_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X2 @ X0 @ X1 @ X3 ) @ ( k2_relset_1 @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('40',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('45',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['29','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ ( sk_E @ X8 @ X9 @ X6 @ X7 ) ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( r1_waybel_0 @ X7 @ X6 @ X9 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('65',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n5PfFdBe1n
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:45:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 80 iterations in 0.059s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.22/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.22/0.54  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.22/0.54  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.22/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(dt_l1_orders_2, axiom,
% 0.22/0.54    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.54  thf('0', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.54  thf('1', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.54  thf(rc7_yellow_6, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ?[B:$i]:
% 0.22/0.54         ( ( v1_yellow_6 @ B @ A ) & ( v7_waybel_0 @ B ) & 
% 0.22/0.54           ( v6_waybel_0 @ B @ A ) & ( v4_orders_2 @ B ) & 
% 0.22/0.54           ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X21 : $i]:
% 0.22/0.54         ((l1_waybel_0 @ (sk_B @ X21) @ X21)
% 0.22/0.54          | ~ (l1_struct_0 @ X21)
% 0.22/0.54          | (v2_struct_0 @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [rc7_yellow_6])).
% 0.22/0.54  thf(dt_k4_yellow_6, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.22/0.54         ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         (~ (l1_struct_0 @ X19)
% 0.22/0.54          | (v2_struct_0 @ X19)
% 0.22/0.54          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.22/0.54          | (m1_subset_1 @ (k4_yellow_6 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k4_yellow_6])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_struct_0 @ X0)
% 0.22/0.54          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.54             (u1_struct_0 @ X0))
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_struct_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (l1_struct_0 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.54  thf(t8_waybel_9, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.54           ( r1_waybel_0 @
% 0.22/0.54             A @ B @ 
% 0.22/0.54             ( k2_relset_1 @
% 0.22/0.54               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.54               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.54              ( r1_waybel_0 @
% 0.22/0.54                A @ B @ 
% 0.22/0.54                ( k2_relset_1 @
% 0.22/0.54                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.54                  ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t8_waybel_9])).
% 0.22/0.54  thf('6', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('7', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.54  thf('8', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (l1_struct_0 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.54  thf(d11_waybel_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.22/0.54               ( ?[D:$i]:
% 0.22/0.54                 ( ( ![E:$i]:
% 0.22/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.54                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.22/0.54                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.22/0.54                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X6)
% 0.22/0.54          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.22/0.54          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X6 @ X7) @ (u1_struct_0 @ X6))
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.22/0.54          | (r1_waybel_0 @ X7 @ X6 @ X9)
% 0.22/0.54          | ~ (l1_struct_0 @ X7)
% 0.22/0.54          | (v2_struct_0 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (l1_struct_0 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | ~ (l1_struct_0 @ X1)
% 0.22/0.54          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.22/0.54          | (m1_subset_1 @ 
% 0.22/0.54             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.22/0.54             (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         (~ (l1_waybel_0 @ X0 @ X1)
% 0.22/0.54          | (m1_subset_1 @ 
% 0.22/0.54             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.22/0.54             (u1_struct_0 @ X0))
% 0.22/0.54          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.22/0.54          | ~ (l1_struct_0 @ X1)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | ~ (l1_struct_0 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B_1)
% 0.22/0.54          | ~ (l1_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (m1_subset_1 @ 
% 0.22/0.54             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54              sk_A) @ 
% 0.22/0.54             (u1_struct_0 @ sk_B_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '12'])).
% 0.22/0.54  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B_1)
% 0.22/0.54          | ~ (l1_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (m1_subset_1 @ 
% 0.22/0.54             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54              sk_A) @ 
% 0.22/0.54             (u1_struct_0 @ sk_B_1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_orders_2 @ sk_B_1)
% 0.22/0.54          | (m1_subset_1 @ 
% 0.22/0.54             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54              sk_A) @ 
% 0.22/0.54             (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '15'])).
% 0.22/0.54  thf('17', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_l1_waybel_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_struct_0 @ A ) =>
% 0.22/0.54       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (l1_waybel_0 @ X15 @ X16)
% 0.22/0.54          | (l1_orders_2 @ X15)
% 0.22/0.54          | ~ (l1_struct_0 @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.22/0.54  thf('19', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('21', plain, ((l1_orders_2 @ sk_B_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ 
% 0.22/0.54           (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54            sk_A) @ 
% 0.22/0.54           (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['16', '21'])).
% 0.22/0.54  thf(d8_waybel_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.54               ( ( k2_waybel_0 @ A @ B @ C ) =
% 0.22/0.54                 ( k3_funct_2 @
% 0.22/0.54                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.54                   ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X12)
% 0.22/0.54          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.22/0.54          | ((k2_waybel_0 @ X13 @ X12 @ X14)
% 0.22/0.54              = (k3_funct_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.22/0.54                 (u1_waybel_0 @ X13 @ X12) @ X14))
% 0.22/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.22/0.54          | ~ (l1_struct_0 @ X13)
% 0.22/0.54          | (v2_struct_0 @ X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [d8_waybel_0])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | ~ (l1_struct_0 @ X1)
% 0.22/0.54          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.22/0.54              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54               sk_A))
% 0.22/0.54              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X1) @ 
% 0.22/0.54                 (u1_waybel_0 @ X1 @ sk_B_1) @ 
% 0.22/0.54                 (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.22/0.54                  sk_B_1 @ sk_A)))
% 0.22/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.22/0.54          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.22/0.54              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54               sk_A))
% 0.22/0.54              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X1) @ 
% 0.22/0.54                 (u1_waybel_0 @ X1 @ sk_B_1) @ 
% 0.22/0.54                 (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.22/0.54                  sk_B_1 @ sk_A)))
% 0.22/0.54          | ~ (l1_struct_0 @ X1)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.54          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54               sk_A))
% 0.22/0.54              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54                 (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54                 (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.22/0.54                  sk_B_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '25'])).
% 0.22/0.54  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54               sk_A))
% 0.22/0.54              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54                 (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54                 (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.22/0.54                  sk_B_1 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54            (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54             sk_A))
% 0.22/0.54            = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54               (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.22/0.54                sk_B_1 @ sk_A)))
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ 
% 0.22/0.54           (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54            sk_A) @ 
% 0.22/0.54           (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['16', '21'])).
% 0.22/0.54  thf('31', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_u1_waybel_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.54       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.22/0.54         ( v1_funct_2 @
% 0.22/0.54           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.54         ( m1_subset_1 @
% 0.22/0.54           ( u1_waybel_0 @ A @ B ) @ 
% 0.22/0.54           ( k1_zfmisc_1 @
% 0.22/0.54             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         (~ (l1_struct_0 @ X17)
% 0.22/0.54          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.22/0.54          | (m1_subset_1 @ (u1_waybel_0 @ X17 @ X18) @ 
% 0.22/0.54             (k1_zfmisc_1 @ 
% 0.22/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17)))))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54         (k1_zfmisc_1 @ 
% 0.22/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.22/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.54  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54        (k1_zfmisc_1 @ 
% 0.22/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf(t189_funct_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.54               ( ![D:$i]:
% 0.22/0.54                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.54                     ( m1_subset_1 @
% 0.22/0.54                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54                   ( r2_hidden @
% 0.22/0.54                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.22/0.54                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ X1)
% 0.22/0.54          | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.22/0.54          | (r2_hidden @ (k3_funct_2 @ X2 @ X0 @ X1 @ X3) @ 
% 0.22/0.54             (k2_relset_1 @ X2 @ X0 @ X1))
% 0.22/0.54          | ~ (m1_subset_1 @ X3 @ X2)
% 0.22/0.54          | (v1_xboole_0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (r2_hidden @ 
% 0.22/0.54             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.54             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54          | ~ (v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1))
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         (~ (l1_struct_0 @ X17)
% 0.22/0.54          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.22/0.54          | (v1_funct_2 @ (u1_waybel_0 @ X17 @ X18) @ (u1_struct_0 @ X18) @ 
% 0.22/0.54             (u1_struct_0 @ X17)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.22/0.54         (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.22/0.54        (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         (~ (l1_struct_0 @ X17)
% 0.22/0.54          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.22/0.54          | (v1_funct_1 @ (u1_waybel_0 @ X17 @ X18)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('47', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (r2_hidden @ 
% 0.22/0.54             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1) @ X0) @ 
% 0.22/0.54             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '42', '47'])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | (r2_hidden @ 
% 0.22/0.54             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.22/0.54              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54               sk_A)) @ 
% 0.22/0.54             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['30', '48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r2_hidden @ 
% 0.22/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54            (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54             sk_A)) @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54          | (v2_struct_0 @ sk_B_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('sup+', [status(thm)], ['29', '49'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_B_1)
% 0.22/0.54          | (r2_hidden @ 
% 0.22/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.22/0.54               sk_A)) @ 
% 0.22/0.54             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54              (u1_waybel_0 @ sk_A @ sk_B_1))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X6)
% 0.22/0.54          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.22/0.54          | ~ (r2_hidden @ 
% 0.22/0.54               (k2_waybel_0 @ X7 @ X6 @ (sk_E @ X8 @ X9 @ X6 @ X7)) @ X9)
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.22/0.54          | (r1_waybel_0 @ X7 @ X6 @ X9)
% 0.22/0.54          | ~ (l1_struct_0 @ X7)
% 0.22/0.54          | (v2_struct_0 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ 
% 0.22/0.54             (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.54  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('55', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ 
% 0.22/0.54             (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      ((~ (m1_subset_1 @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ 
% 0.22/0.54           (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1)
% 0.22/0.54        | ~ (l1_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '57'])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (l1_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      ((~ (l1_orders_2 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '59'])).
% 0.22/0.54  thf('61', plain, ((l1_orders_2 @ sk_B_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.54          (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54           (u1_waybel_0 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.54  thf(fc2_struct_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      (![X4 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.22/0.54          | ~ (l1_struct_0 @ X4)
% 0.22/0.54          | (v2_struct_0 @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.54  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['68'])).
% 0.22/0.54  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('71', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.22/0.54      inference('clc', [status(thm)], ['69', '70'])).
% 0.22/0.54  thf('72', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('73', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('clc', [status(thm)], ['71', '72'])).
% 0.22/0.54  thf('74', plain,
% 0.22/0.54      (![X4 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.22/0.54          | ~ (l1_struct_0 @ X4)
% 0.22/0.54          | (v2_struct_0 @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.54  thf('75', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.54  thf('76', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('77', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.22/0.54      inference('clc', [status(thm)], ['75', '76'])).
% 0.22/0.54  thf('78', plain, (~ (l1_orders_2 @ sk_B_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '77'])).
% 0.22/0.54  thf('79', plain, ((l1_orders_2 @ sk_B_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('80', plain, ($false), inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
