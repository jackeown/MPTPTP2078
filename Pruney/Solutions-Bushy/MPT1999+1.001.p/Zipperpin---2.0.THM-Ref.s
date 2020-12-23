%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1999+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qn8tXNeJVk

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:39 EST 2020

% Result     : Theorem 3.64s
% Output     : Refutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 650 expanded)
%              Number of leaves         :   46 ( 203 expanded)
%              Depth                    :   26
%              Number of atoms          : 3014 (18802 expanded)
%              Number of equality atoms :   24 (  54 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_waybel_3_type,type,(
    v3_waybel_3: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_waybel_3_type,type,(
    r1_waybel_3: $i > $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_waybel_7_type,type,(
    v5_waybel_7: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k1_waybel_4_type,type,(
    k1_waybel_4: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t48_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v4_waybel_7 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r1_waybel_3 @ A @ ( k12_lattice3 @ A @ C @ D ) @ B )
                          & ~ ( r3_orders_2 @ A @ C @ B )
                          & ~ ( r3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_waybel_3 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
             => ( ( v4_waybel_7 @ B @ A )
              <=> ! [C: $i] :
                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                   => ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r1_waybel_3 @ A @ ( k12_lattice3 @ A @ C @ D ) @ B )
                            & ~ ( r3_orders_2 @ A @ C @ B )
                            & ~ ( r3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_waybel_7])).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
      | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
      | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_waybel_7 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l57_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r1_waybel_3 @ A @ ( k12_lattice3 @ A @ C @ D ) @ B )
                          & ~ ( r3_orders_2 @ A @ C @ B )
                          & ~ ( r3_orders_2 @ A @ D @ B ) ) ) )
              & ~ ( v5_waybel_6 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( v5_waybel_6 @ X16 @ X17 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X17 ) @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v3_waybel_3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v3_waybel_3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9','10','11','12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( v5_waybel_6 @ X16 @ X17 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X17 ) @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v3_waybel_3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v3_waybel_3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25','26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r1_waybel_3 @ X17 @ ( k12_lattice3 @ X17 @ ( sk_C @ X16 @ X17 ) @ ( sk_D_1 @ X16 @ X17 ) ) @ X16 )
      | ( v5_waybel_6 @ X16 @ X17 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X17 ) @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v3_waybel_3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('32',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A )
    | ( v5_waybel_6 @ sk_B @ sk_A )
    | ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
    | ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ( v5_waybel_6 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( v5_waybel_6 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v5_waybel_6 @ sk_B @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,
    ( ( ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v5_waybel_6 @ sk_B @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( v5_waybel_6 @ sk_B @ sk_A )
      | ( v5_waybel_6 @ sk_B @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','46'])).

thf('48',plain,
    ( ( ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v5_waybel_6 @ sk_B @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_orders_2 @ X17 @ ( sk_D_1 @ X16 @ X17 ) @ X16 )
      | ( v5_waybel_6 @ X16 @ X17 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X17 ) @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v3_waybel_3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('51',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A )
    | ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57','58','59','60'])).

thf('62',plain,
    ( ( ( v5_waybel_6 @ sk_B @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['48','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_orders_2 @ X17 @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v5_waybel_6 @ X16 @ X17 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X17 ) @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v3_waybel_3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v1_yellow_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('65',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A )
    | ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70','71','72','73','74'])).

thf('76',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['62','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v4_waybel_7 @ B @ A ) ) ) ) )).

thf('78',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v4_waybel_7 @ X21 @ X22 )
      | ~ ( v5_waybel_6 @ X21 @ X22 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v2_lattice3 @ X22 )
      | ~ ( v1_lattice3 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_waybel_7])).

thf('79',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85'])).

thf('87',plain,
    ( ( v4_waybel_7 @ sk_B @ sk_A )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
        | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
        | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v4_waybel_7 @ sk_B @ sk_A )
   <= ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ~ ! [X30: $i,X31: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_orders_2 @ sk_A @ X30 @ sk_B )
          | ( r3_orders_2 @ sk_A @ X31 @ sk_B )
          | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X30 @ X31 ) @ sk_B )
          | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['88'])).

thf('94',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( v4_waybel_7 @ sk_B @ sk_A )
   <= ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
   <= ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['91'])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['88'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['98'])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('104',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k7_domain_1 @ X19 @ X18 @ X20 )
        = ( k2_tarski @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
          = ( k2_tarski @ sk_C_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_3 )
        = ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['88'])).

thf('108',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['98'])).

thf(t40_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k2_yellow_0 @ A @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k12_lattice3 @ A @ B @ C ) ) ) ) ) )).

thf('109',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( k2_yellow_0 @ X27 @ ( k7_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X28 ) )
        = ( k12_lattice3 @ X27 @ X26 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t40_yellow_0])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) )
          = ( k12_lattice3 @ sk_A @ sk_C_1 @ X0 ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) )
          = ( k12_lattice3 @ sk_A @ sk_C_1 @ X0 ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115'])).

thf('117',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_3 ) )
      = ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,
    ( ( ( ( k2_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        = ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['106','117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_3 )
        = ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['88'])).

thf('121',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['98'])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('122',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,
    ( ( ( m1_subset_1 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf(t39_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v4_waybel_7 @ B @ A )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v1_finset_1 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ( r1_waybel_3 @ A @ ( k2_yellow_0 @ A @ C ) @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ( r3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('127',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r2_hidden @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_waybel_3 @ X24 @ ( k2_yellow_0 @ X24 @ X25 ) @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_finset_1 @ X25 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v4_waybel_7 @ X23 @ X24 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v3_waybel_3 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_waybel_7])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v3_waybel_3 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( v1_finset_1 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( r1_waybel_3 @ sk_A @ ( k2_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) @ X0 )
        | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_finset_1 @ ( k2_tarski @ A @ B ) ) )).

thf('136',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_finset_1 @ ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_finset_1])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( r1_waybel_3 @ sk_A @ ( k2_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) @ X0 )
        | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134','135','136'])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ~ ( v4_waybel_7 @ sk_B @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ~ ( v4_waybel_7 @ sk_B @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','142'])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('144',plain,(
    ! [X14: $i,X15: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('145',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('146',plain,(
    ! [X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ( X5 = X4 )
      | ( X5 = X1 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('147',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( X5 = X1 )
      | ( X5 = X4 )
      | ~ ( r2_hidden @ X5 @ ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A )
        = sk_C_1 )
      | ( ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A )
        = sk_D_3 ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,
    ( ( v4_waybel_7 @ sk_B @ sk_A )
   <= ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
   <= ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['91'])).

thf('151',plain,
    ( ( ( ( k2_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        = ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['106','117'])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('153',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r3_orders_2 @ X24 @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ X23 )
      | ~ ( r1_waybel_3 @ X24 @ ( k2_yellow_0 @ X24 @ X25 ) @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_finset_1 @ X25 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v4_waybel_7 @ X23 @ X24 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v3_waybel_3 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_waybel_7])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v3_waybel_3 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( v1_finset_1 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( r1_waybel_3 @ sk_A @ ( k2_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) @ X0 )
        | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_finset_1 @ ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_finset_1])).

thf('163',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( r1_waybel_3 @ sk_A @ ( k2_yellow_0 @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) ) @ X0 )
        | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159','160','161','162'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ X0 )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['151','163'])).

thf('165',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_waybel_7 @ X0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
        | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ X0 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ~ ( v4_waybel_7 @ sk_B @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ~ ( v4_waybel_7 @ sk_B @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( v1_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['149','168'])).

thf('170',plain,(
    ! [X14: $i,X15: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('171',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      | ( ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A )
        = sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['148','171'])).

thf('173',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A )
        = sk_C_1 )
      | ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_D_2 @ ( k2_tarski @ sk_C_1 @ sk_D_3 ) @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('175',plain,
    ( ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
   <= ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['94'])).

thf('178',plain,
    ( ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      & ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['96'])).

thf('180',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      & ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('181',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      & ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('184',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('185',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ~ ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      & ( v4_waybel_7 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['182','185'])).

thf('187',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('189',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_C_1 @ sk_D_3 ) @ sk_B )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A )
    | ( r3_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','90','92','93','95','97','99','192'])).


%------------------------------------------------------------------------------
