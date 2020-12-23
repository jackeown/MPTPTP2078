%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bi1VnpUJjo

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:38 EST 2020

% Result     : Theorem 25.79s
% Output     : Refutation 25.82s
% Verified   : 
% Statistics : Number of formulae       :  382 (1896 expanded)
%              Number of leaves         :   41 ( 561 expanded)
%              Depth                    :   52
%              Number of atoms          : 6514 (55736 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_waybel_1_type,type,(
    v2_waybel_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_waybel_3_type,type,(
    r1_waybel_3: $i > $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v25_waybel_0_type,type,(
    v25_waybel_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v24_waybel_0_type,type,(
    v24_waybel_0: $i > $o )).

thf(t36_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_waybel_3 @ A @ B @ C )
              <=> ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( v1_waybel_0 @ D @ A )
                      & ( v12_waybel_0 @ D @ A )
                      & ( v1_waybel_7 @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ( ( r3_orders_2 @ A @ C @ ( k1_yellow_0 @ A @ D ) )
                     => ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v2_waybel_1 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_waybel_3 @ A @ B @ C )
                <=> ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v1_waybel_0 @ D @ A )
                        & ( v12_waybel_0 @ D @ A )
                        & ( v1_waybel_7 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ( ( r3_orders_2 @ A @ C @ ( k1_yellow_0 @ A @ D ) )
                       => ( r2_hidden @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_waybel_7])).

thf('0',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v12_waybel_0 @ sk_D_2 @ sk_A )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v12_waybel_0 @ sk_D_2 @ sk_A )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v1_waybel_0 @ sk_D_2 @ sk_A )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_waybel_0 @ sk_D_2 @ sk_A )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_waybel_0 @ X24 @ sk_A )
      | ~ ( v12_waybel_0 @ X24 @ sk_A )
      | ~ ( v1_waybel_7 @ X24 @ sk_A )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ sk_B @ X24 )
      | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
   <= ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( v1_waybel_0 @ sk_D_2 @ sk_A )
   <= ( v1_waybel_0 @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('17',plain,
    ( ( v12_waybel_0 @ sk_D_2 @ sk_A )
   <= ( v12_waybel_0 @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t20_waybel_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_waybel_3 @ A @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( v1_waybel_0 @ D @ A )
                      & ( v12_waybel_0 @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ( ( r3_orders_2 @ A @ C @ ( k1_yellow_0 @ A @ D ) )
                     => ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_waybel_3 @ X8 @ X7 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_waybel_0 @ X10 @ X8 )
      | ~ ( v12_waybel_0 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r2_hidden @ X7 @ X10 )
      | ~ ( r3_orders_2 @ X8 @ X9 @ ( k1_yellow_0 @ X8 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_waybel_3])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r3_orders_2 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
        | ( r2_hidden @ X1 @ sk_D_2 )
        | ~ ( v12_waybel_0 @ sk_D_2 @ sk_A )
        | ~ ( v1_waybel_0 @ sk_D_2 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( r1_waybel_3 @ sk_A @ X1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r3_orders_2 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
        | ( r2_hidden @ X1 @ sk_D_2 )
        | ~ ( v12_waybel_0 @ sk_D_2 @ sk_A )
        | ~ ( v1_waybel_0 @ sk_D_2 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( r1_waybel_3 @ sk_A @ X1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_3 @ sk_A @ X0 @ X1 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( v1_waybel_0 @ sk_D_2 @ sk_A )
        | ( r2_hidden @ X0 @ sk_D_2 )
        | ~ ( r3_orders_2 @ sk_A @ X1 @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r3_orders_2 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
        | ( r2_hidden @ X1 @ sk_D_2 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( r1_waybel_3 @ sk_A @ X1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_3 @ sk_A @ X0 @ sk_C )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( r2_hidden @ X0 @ sk_D_2 )
        | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_3 @ sk_A @ X0 @ sk_C )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( r2_hidden @ X0 @ sk_D_2 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ sk_D_2 )
      | ( v1_xboole_0 @ sk_D_2 )
      | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( r2_hidden @ sk_B @ sk_D_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      & ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X1: $i] :
      ( ~ ( v2_lattice3 @ X1 )
      | ~ ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('34',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( r2_hidden @ sk_B @ sk_D_2 )
      | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      & ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      & ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v12_waybel_0 @ sk_D_2 @ sk_A )
      & ( v1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
   <= ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('41',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ sk_D_2 ) )
    | ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ~ ( v1_waybel_0 @ sk_D_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v12_waybel_0 @ sk_D_2 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_D_2 )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_waybel_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v24_waybel_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( v1_waybel_0 @ D @ A )
                      & ( v12_waybel_0 @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ( ( r3_orders_2 @ A @ C @ ( k1_yellow_0 @ A @ D ) )
                     => ( r2_hidden @ B @ D ) ) )
               => ( r1_waybel_3 @ A @ B @ C ) ) ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( v1_waybel_0 @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 )
      | ( r1_waybel_3 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v24_waybel_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_3])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v3_lattice3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v24_waybel_0 @ A )
          & ( v25_waybel_0 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc11_waybel_0])).

thf('53',plain,
    ( ( v24_waybel_0 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v24_waybel_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('58',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','58','59'])).

thf('61',plain,
    ( ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('63',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( v12_waybel_0 @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 )
      | ( r1_waybel_3 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v24_waybel_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_3])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,
    ( ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('76',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_waybel_3 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v24_waybel_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_3])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('89',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf(t28_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ~ ( r2_hidden @ C @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v1_waybel_0 @ D @ A )
                        & ( v12_waybel_0 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( v1_waybel_7 @ D @ A )
                          & ( r1_tarski @ B @ D )
                          & ~ ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ X19 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('107',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('108',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('109',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ X19 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
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
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v12_waybel_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v12_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('126',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('127',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('128',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ X19 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_waybel_7 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_waybel_7 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('145',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('146',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('147',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153','154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['145','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['144','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','160'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('162',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('163',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('164',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('166',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('167',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('168',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ X18 @ ( sk_D_1 @ X20 @ X18 @ X19 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174','175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','181'])).

thf(t3_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
            & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) )).

thf('183',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r3_orders_2 @ X23 @ ( k1_yellow_0 @ X23 @ X21 ) @ ( k1_yellow_0 @ X23 @ X22 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v3_lattice3 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_waybel_7])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ X0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('186',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('187',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r3_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['185','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ X0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ X0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r3_orders_2 @ X12 @ X13 @ ( k1_yellow_0 @ X12 @ ( sk_D @ X13 @ X11 @ X12 ) ) )
      | ( r1_waybel_3 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v24_waybel_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_3])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('203',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203'])).

thf('205',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('207',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r3_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['207','213'])).

thf('215',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['194','214'])).

thf('216',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('219',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('221',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_orders_2 @ A @ B @ C )
                      & ( r1_orders_2 @ A @ C @ D ) )
                   => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('222',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X17 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['220','226'])).

thf('228',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['219','229'])).

thf('231',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['193','230'])).

thf('232',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['231','232','233','234','235','236','237','238'])).

thf('240',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','240'])).

thf('242',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r3_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['243','249'])).

thf('251',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['162','251'])).

thf('253',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,
    ( ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('256',plain,
    ( ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_waybel_7 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_7 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['161','256'])).

thf('258',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_7 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v12_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['142','258'])).

thf('260',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['123','260'])).

thf('262',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['104','262'])).

thf('264',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('266',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('267',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('268',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r2_hidden @ X20 @ ( sk_D_1 @ X20 @ X18 @ X19 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['269','270','271','272','273','274','275','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['266','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['265','279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['264','281'])).

thf('283',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_D_1 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('287',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('288',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('289',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( v12_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X20 @ X18 @ X19 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v1_lattice3 @ X19 )
      | ~ ( v2_waybel_1 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_waybel_7])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['290','291','292','293','294','295','296','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['287','298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['286','300'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['285','302'])).

thf('304',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(demod,[status(thm)],['303','304'])).

thf('306',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ ( sk_D @ X13 @ X11 @ X12 ) )
      | ( r1_waybel_3 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v24_waybel_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_3])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('314',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['309','310','311','312','313','314'])).

thf('316',plain,
    ( ( ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['306','315'])).

thf('317',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(demod,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('321',plain,
    ( ( ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('322',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_xboole_0 @ ( sk_D @ X13 @ X11 @ X12 ) )
      | ( r1_waybel_3 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v24_waybel_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_3])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v24_waybel_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    v24_waybel_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('329',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_3 @ sk_A @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['324','325','326','327','328','329'])).

thf('331',plain,
    ( ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['321','330'])).

thf('332',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('336',plain,
    ( ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
   <= ! [X24: $i] :
        ( ( v1_xboole_0 @ X24 )
        | ~ ( v1_waybel_0 @ X24 @ sk_A )
        | ~ ( v12_waybel_0 @ X24 @ sk_A )
        | ~ ( v1_waybel_7 @ X24 @ sk_A )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ sk_B @ X24 )
        | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) ) ),
    inference(clc,[status(thm)],['334','335'])).

thf('337',plain,
    ( ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('338',plain,
    ( ~ ! [X24: $i] :
          ( ( v1_xboole_0 @ X24 )
          | ~ ( v1_waybel_0 @ X24 @ sk_A )
          | ~ ( v12_waybel_0 @ X24 @ sk_A )
          | ~ ( v1_waybel_7 @ X24 @ sk_A )
          | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( r2_hidden @ sk_B @ X24 )
          | ~ ( r3_orders_2 @ sk_A @ sk_C @ ( k1_yellow_0 @ sk_A @ X24 ) ) )
    | ( r1_waybel_3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','41','42','338'])).


%------------------------------------------------------------------------------
